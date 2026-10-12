import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.boxPiSet_proj
import Submission.Work.BoseBoxFock.boxPiSet_sum_setIntegral
import Submission.Work.BoseBoxFock.sliceDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.setIntegral_confY13_slice`

The slice identity of the `Y`-configuration of the block I / III.1 fibre `pairG13`:

    ∫ y in boxL ℓ, ∫ x' in boxPiSet {k // k ≠ p.2} ℓ, ∫ u in boxL ℓ, f (confY13 p y u x')
      = ℓ^3 · ∫ x in abox n ℓ, f x .

The point is that the middle variable `x' : {k : Fin n // k ≠ p.2} → E3` carries **one redundant
coordinate** — the coordinate `p.1`, which `confY13` overwrites by `y`.  Consequently the left
side is the integral of `f` over the *(n+1)*-fold box `boxL^{n+1}` pulled back along the
configuration map `(y, x', u) ↦ confY13 p y u x'`, and its fibres are exactly the box `boxL ℓ` of
the forgotten coordinate; hence the factor `ℓ^3 = vol (boxL ℓ)`.

Formally, with `ι := {k : Fin n // k ≠ p.2}` the configuration map is the composition

    Unit ⊕ (ι ⊕ Unit)  --(confIdx p)-->  Fin n ,      a ↦ fun k => a (confIdx p k) ,

where `confIdx p` is the injection selecting, for each `k : Fin n`, the domain coordinate carrying
the value of `confY13` at `k`:

* `k = p.1` ← the `y`-coordinate (the first `Unit`),
* `k = p.2` ← the `u`-coordinate (the last `Unit`),
* all other `k` ← the `x'`-coordinate of `ι`.

`confIdx p` misses exactly the coordinate `Sum.inr (Sum.inl ⟨p.1, hp⟩)` of `ι`, so the complement
has cardinality `1` and `boxPiSet_proj` produces the factor `ℓ^(3·1) = ℓ^3`.

Implemented with the general box lemmas
`Work.BoseBoxFock.boxPiSet_proj` (projection along an injection of index types) and
`Work.BoseBoxFock.boxPiSet_sum_setIntegral` (Fubini for `boxPiSet` over a sum index type),
plus the elementary `Unit`-factor and expansion lemmas below.
-/

noncomputable section

open MeasureTheory

namespace Work.BoseBoxFock

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "Xn" => Work.BoseDict.Xn
local notation "boxL" => Work.BoseK15.corpusBox.boxL

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## 0. The "cons" map is continuous -/

/-- Inserting a fixed configuration in the first summand of an index type is continuous. -/
lemma continuous_sumElim_cons {τ₁ τ₂ : Type*} [Fintype τ₁] [Fintype τ₂]
    (b : τ₁ → E3) : Continuous (fun c : τ₂ → E3 => (Sum.elim b c : τ₁ ⊕ τ₂ → E3)) := by
  rw [continuous_pi_iff]
  intro j
  rcases j with i | i
  · simp only [Sum.elim_inl]; exact continuous_const
  · simp only [Sum.elim_inr]; exact continuous_apply i

/-! ## 1. The `Unit`-factor of a box integral -/

/-- A `boxPiSet` integral over the one-element index type `Unit` is an integral over `boxL ℓ`. -/
lemma boxPiSet_unit_setIntegral {ℓ : ℝ} (H : (Unit → E3) → ℝ) :
    (∫ b in boxPiSet Unit ℓ, H b) = ∫ y in boxL ℓ, H (fun _ => y) := by
  rw [restrict_boxPiSet_eq]
  have h := (measurePreserving_funUnique (boxMeas ℓ) Unit).integral_comp'
    (fun y : E3 => H (fun _ => y))
  rw [MeasurableEquiv.funUnique_apply] at h
  rw [← h]

/-- Fubini for `boxPiSet` over a sum with the `Unit` summand **first**, with the `Unit` variable
integrated against `boxL ℓ` (i.e. the `ℓ^3`-factor made explicit). -/
lemma boxPiSet_cons_setIntegral {τ : Type*} [Fintype τ] {ℓ : ℝ} (hℓ : 0 < ℓ)
    (G : (Unit ⊕ τ → E3) → ℝ) (hG : Continuous G) :
    (∫ a in boxPiSet (Unit ⊕ τ) ℓ, G a)
      = ∫ y in boxL ℓ, ∫ c in boxPiSet τ ℓ, G (Sum.elim (fun _ => y) c) := by
  rw [boxPiSet_sum_setIntegral hℓ G hG]
  rw [boxPiSet_unit_setIntegral]

/-- Fubini for `boxPiSet` over a sum with the `Unit` summand **last**, with the `Unit` variable
integrated against `boxL ℓ`. -/
lemma boxPiSet_snoc_setIntegral {τ : Type*} [Fintype τ] {ℓ : ℝ} (hℓ : 0 < ℓ)
    (G : (τ ⊕ Unit → E3) → ℝ) (hG : Continuous G) :
    (∫ a in boxPiSet (τ ⊕ Unit) ℓ, G a)
      = ∫ c in boxPiSet τ ℓ, ∫ u in boxL ℓ, G (Sum.elim c (fun _ => u)) := by
  rw [boxPiSet_sum_setIntegral hℓ G hG]
  refine integral_congr_ae (Filter.Eventually.of_forall (fun c => ?_))
  exact boxPiSet_unit_setIntegral (H := fun d => G (Sum.elim c d))

/-! ## 2. The index insertion `confIdx` -/

/-- **The index insertion of the `Y`-configuration**: `k ↦` the domain coordinate of
`Unit ⊕ ({k // k ≠ p.2} ⊕ Unit)` that carries the value `confY13 p y u x' k`. -/
def confIdx {n : ℕ} (p : Fin n × Fin n) : Fin n → Unit ⊕ ({k : Fin n // k ≠ p.2} ⊕ Unit) :=
  fun k => if _ : k = p.1 then Sum.inl ()
           else if h2 : k = p.2 then Sum.inr (Sum.inr ())
           else Sum.inr (Sum.inl ⟨k, h2⟩)

/-- The left inverse of `confIdx p`: read off the coordinate of `k` from the domain index. -/
def confIdxInv {n : ℕ} (p : Fin n × Fin n) :
    (Unit ⊕ ({k : Fin n // k ≠ p.2} ⊕ Unit)) → Fin n
  | Sum.inl _ => p.1
  | Sum.inr (Sum.inl k) => k.1
  | Sum.inr (Sum.inr _) => p.2

lemma confIdxInv_confIdx {n : ℕ} (p : Fin n × Fin n) (k : Fin n) :
    confIdxInv p (confIdx p k) = k := by
  rw [confIdx]
  by_cases h1 : k = p.1
  · rw [dif_pos h1]; exact h1.symm
  · by_cases h2 : k = p.2
    · rw [dif_neg h1, dif_pos h2]; exact h2.symm
    · rw [dif_neg h1, dif_neg h2]; rfl

/-- `confIdx p` is injective. -/
lemma confIdx_injective {n : ℕ} (p : Fin n × Fin n) : Function.Injective (confIdx p) := by
  intro a b hab
  rw [← confIdxInv_confIdx p a, ← confIdxInv_confIdx p b, hab]

/-- **The pointwise identification**: reading the `confIdx p`-coordinates of the inserted data
`(y, x', u)` reproduces the `Y`-configuration `confY13 p y u x'`. -/
lemma confIdx_confY13 {n : ℕ} (p : Fin n × Fin n) (y u : E3)
    (x' : {k : Fin n // k ≠ p.2} → E3) :
    (fun k => Sum.elim (fun _ => y) (Sum.elim x' (fun _ => u)) (confIdx p k))
      = confY13 p y u x' := by
  funext k
  simp only [confIdx]
  by_cases h1 : k = p.1
  · subst h1; simp [confY13]
  · by_cases h2 : k = p.2
    · subst h2; simp [confY13, h1]
    · simp [confY13, h1, h2]

/-- Continuity of the coordinate projection `a ↦ (k ↦ a (confIdx p k))`. -/
lemma continuous_confIdx_comp {n : ℕ} (p : Fin n × Fin n) :
    Continuous (fun a : (Unit ⊕ ({k : Fin n // k ≠ p.2} ⊕ Unit)) → E3 =>
      fun k => a (confIdx p k)) := by
  rw [continuous_pi_iff]
  intro k
  exact continuous_apply (confIdx p k)

/-! ## 3. The cardinality of the forgotten coordinate -/

/-- The index insertion `confIdx p` misses exactly one coordinate, so the complement has
cardinality `1` (equivalently `#(Unit ⊕ (ι ⊕ Unit)) = #(Fin n) + 1`). -/
lemma card_confIdx_compl {n : ℕ} (p : Fin n × Fin n) (hp : p.1 ≠ p.2) :
    Fintype.card (Unit ⊕ ({k : Fin n // k ≠ p.2} ⊕ Unit)) - Fintype.card (Fin n) = 1 := by
  have hn : 2 ≤ n := by
    haveI : Nontrivial (Fin n) := ⟨p.1, p.2, hp⟩
    have h := Fintype.one_lt_card (α := Fin n)
    simp at h
    omega
  have hcard1 : Fintype.card {k : Fin n // k = p.2} = 1 := by
    rw [Fintype.card_eq_one_iff]
    exact ⟨⟨p.2, rfl⟩, fun y => Subtype.ext y.2⟩
  have hc : Fintype.card {k : Fin n // k ≠ p.2} = n - 1 := by
    have h := Fintype.card_subtype_compl (α := Fin n) (p := fun k : Fin n => k = p.2)
    simp only [Fintype.card_fin] at h
    rw [h, hcard1]
  rw [Fintype.card_sum, Fintype.card_sum, Fintype.card_unit, Fintype.card_fin, hc]
  omega

/-! ## 4. The expansion of the left-hand side -/

/-- The left-hand side of the slice identity, written as a single `boxPiSet` integral over the
index type `Unit ⊕ (ι ⊕ Unit)` of the coordinate projection `a ↦ a ∘ confIdx p`. -/
lemma boxPiSet_confY13_expand {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) (p : Fin n × Fin n)
    {f : Xn n → ℝ} (hf : Continuous f) :
    (∫ a in boxPiSet (Unit ⊕ ({k : Fin n // k ≠ p.2} ⊕ Unit)) ℓ,
        f (fun k => a (confIdx p k)))
      = ∫ y in boxL ℓ, ∫ x' in boxPiSet ({k : Fin n // k ≠ p.2}) ℓ,
          ∫ u in boxL ℓ, f (confY13 p y u x') := by
  have h1 : (∫ a in boxPiSet (Unit ⊕ ({k : Fin n // k ≠ p.2} ⊕ Unit)) ℓ,
        f (fun k => a (confIdx p k)))
      = ∫ y in boxL ℓ, ∫ c in boxPiSet ({k : Fin n // k ≠ p.2} ⊕ Unit) ℓ,
          f (fun k => (Sum.elim (fun _ => y) c) (confIdx p k)) :=
    boxPiSet_cons_setIntegral hℓ (fun a => f (fun k => a (confIdx p k)))
      (hf.comp (continuous_confIdx_comp p))
  rw [h1]
  refine integral_congr_ae (Filter.Eventually.of_forall (fun y => ?_))
  have h2 : (∫ c in boxPiSet ({k : Fin n // k ≠ p.2} ⊕ Unit) ℓ,
        f (fun k => (Sum.elim (fun _ => y) c) (confIdx p k)))
      = ∫ x' in boxPiSet ({k : Fin n // k ≠ p.2}) ℓ, ∫ u in boxL ℓ,
          f (fun k => (Sum.elim (fun _ => y) (Sum.elim x' (fun _ => u))) (confIdx p k)) :=
    boxPiSet_snoc_setIntegral hℓ
      (fun c => f (fun k => (Sum.elim (fun _ => y) c) (confIdx p k)))
      (hf.comp ((continuous_confIdx_comp p).comp (continuous_sumElim_cons (fun _ : Unit => y))))
  have h3 : (∫ x' in boxPiSet ({k : Fin n // k ≠ p.2}) ℓ, ∫ u in boxL ℓ,
        f (fun k => (Sum.elim (fun _ => y) (Sum.elim x' (fun _ => u))) (confIdx p k)))
      = ∫ x' in boxPiSet ({k : Fin n // k ≠ p.2}) ℓ, ∫ u in boxL ℓ, f (confY13 p y u x') := by
    refine integral_congr_ae (Filter.Eventually.of_forall (fun x' => ?_))
    refine integral_congr_ae (Filter.Eventually.of_forall (fun u => ?_))
    exact congrArg f (confIdx_confY13 p y u x')
  exact h2.trans h3

/-! ## 5. The slice identity -/

theorem setIntegral_confY13_slice {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) (p : Fin n × Fin n)
    (hp : p.1 ≠ p.2) {f : Work.BoseDict.Xn n → ℝ} (hf : Continuous f) :
    (∫ y in Work.BoseK15.corpusBox.boxL ℓ,
        ∫ x' in boxPiSet ({k : Fin n // k ≠ p.2}) ℓ, ∫ u in Work.BoseK15.corpusBox.boxL ℓ,
          f (confY13 p y u x'))
      = ℓ ^ 3 * ∫ x in Submission.BoseGases.abox n ℓ, f x := by
  have hbox : boxPiSet (Fin n) ℓ = Submission.BoseGases.abox n ℓ := by
    ext x
    simp only [mem_boxPiSet, Submission.BoseGases.mem_abox_iff, corpusBox_boxL_eq_acube hℓ]
  calc (∫ y in Work.BoseK15.corpusBox.boxL ℓ,
        ∫ x' in boxPiSet ({k : Fin n // k ≠ p.2}) ℓ, ∫ u in Work.BoseK15.corpusBox.boxL ℓ,
          f (confY13 p y u x'))
      = ∫ a in boxPiSet (Unit ⊕ ({k : Fin n // k ≠ p.2} ⊕ Unit)) ℓ,
          f (fun k => a (confIdx p k)) := (boxPiSet_confY13_expand hℓ p hf).symm
    _ = ℓ ^ (3 * (Fintype.card (Unit ⊕ ({k : Fin n // k ≠ p.2} ⊕ Unit))
            - Fintype.card (Fin n))) * ∫ q in boxPiSet (Fin n) ℓ, f q :=
          boxPiSet_proj hℓ (confIdx p) (confIdx_injective p) f hf
    _ = ℓ ^ 3 * ∫ q in boxPiSet (Fin n) ℓ, f q := by
          rw [card_confIdx_compl p hp, Nat.mul_one]
    _ = ℓ ^ 3 * ∫ x in Submission.BoseGases.abox n ℓ, f x := by rw [hbox]

end Work.BoseBoxFock
