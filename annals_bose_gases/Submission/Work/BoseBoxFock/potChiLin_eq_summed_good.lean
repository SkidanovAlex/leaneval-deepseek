import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.chiTailDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.potChiLin_eq_summed_good` — the collapse of the two `Q₁` mode sums

`Work.BoseBoxFock.potChiLin B f g E` is FS `lem:2ndQuand`'s `Q₁` row written as a sum over the
lattice modes `k` of the χ-row (weights `hatChi k`, modes `f k`) and over the excited lattice modes
(the χ²-row, weights `hatChiSq s`, modes `g s`).  Since the map `T ↦ B T` is *linear in the
one-body operator* `T` — in particular for `B = fun T => boxSlotSum e T` — the two mode sums can be
collapsed into the single superposed modes

    c  = ∑_k hatChi k • f k ,        c' = ∑_{s ≠ 0} hatChiSq s • g s

This is the identity

    potChiLin B f g E = potChiLinSummed B c c' E ,

whose proof is finite `Finset` algebra in the one-body argument, together with the *linearity of
`boxSlotSum e T` in its state argument* on measurable, everywhere bounded states
(`Work.MB.boxSlotSum_bdd`) — needed for the two-letter products such as
`B (|e₀⟩⟨e₀|) ∘ B (|f_k⟩⟨e₀|)`, since those are maps of the *state*.

The hypotheses on `e` and `Θ` are exactly those making the slot integrals honest (measurable,
everywhere bounded, supported in the corpus box); they are not needed for the collapse itself but
are what the consumer supplies.

Everything here is `sorry`-free.
-/

noncomputable section

open scoped BigOperators

namespace Work.BoseBoxFock

open Work.BoseB4 Work.BoseDict

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 4000000

variable {m : ℕ}

/-! ## 1. Scalar bookkeeping on `ℂ` -/

/-- Real and complex scalar multiplication agree on `ℂ`. -/
private lemma real_smul_eq_complex_smul (r : ℝ) (z : ℂ) : r • z = (r : ℂ) • z := by
  rw [smul_eq_mul, Complex.real_smul]

/-- A scalar distributes over a finite sum of scalar multiples, *keeping the scalar on the right
factor*: `r • ∑_k c_k • K_k = ∑_k c_k • (r • K_k)`.  This is the form in which the real prefactors
`ℓ⁻³Ŵ₁(0)`, `μŴ₁(0)`, `ℓ⁻³Ŵ₁ω(0)` of `potChiLin` occur. -/
private lemma smul_finset_sum_smul {V : Type*} [AddCommGroup V] [Module ℝ V] {κ : Type*}
    (s : Finset κ) (r : ℝ) (c : κ → ℝ) (K : κ → V) :
    r • (∑ k ∈ s, c k • K k) = ∑ k ∈ s, c k • (r • K k) := by
  rw [Finset.smul_sum]
  exact Finset.sum_congr rfl fun k _ => smul_comm r (c k) (K k)

/-! ## 2. `rankOnePair` is linear in each argument -/

/-- `rankOnePair · v` is linear over a finite sum. -/
private theorem rankOnePair_finset_sum_left {κ : Type*} (s : Finset κ) (c : κ → ℝ)
    (u : κ → Fin m → ℝ) (v : Fin m → ℝ) :
    rankOnePair (∑ k ∈ s, c k • u k) v = ∑ k ∈ s, c k • rankOnePair (u k) v := by
  refine LinearMap.ext fun x => ?_
  funext i
  simp only [rankOnePair_apply, LinearMap.sum_apply, LinearMap.smul_apply, Pi.smul_apply,
    Finset.sum_apply, smul_eq_mul]
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun k _ => by ring

/-- `rankOnePair w ·` is linear over a finite sum. -/
private theorem rankOnePair_finset_sum_right {κ : Type*} (s : Finset κ) (c : κ → ℝ)
    (w : Fin m → ℝ) (v : κ → Fin m → ℝ) :
    rankOnePair w (∑ k ∈ s, c k • v k) = ∑ k ∈ s, c k • rankOnePair w (v k) := by
  refine LinearMap.ext fun x => ?_
  funext i
  simp only [rankOnePair_apply, LinearMap.sum_apply, LinearMap.smul_apply, Pi.smul_apply,
    Finset.sum_apply, smul_eq_mul]
  have h1 : (∑ l : Fin m, (∑ k ∈ s, c k * v k l) * x l)
      = ∑ l : Fin m, ∑ k ∈ s, (c k * v k l) * x l :=
    Finset.sum_congr rfl fun l _ => Finset.sum_mul ..
  have h2 : (∑ l : Fin m, ∑ k ∈ s, (c k * v k l) * x l)
      = ∑ k ∈ s, ∑ l : Fin m, (c k * v k l) * x l := Finset.sum_comm
  have h3 : (∑ k ∈ s, ∑ l : Fin m, (c k * v k l) * x l)
      = ∑ k ∈ s, c k * (∑ l : Fin m, v k l * x l) := by
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun l _ => by ring
  rw [h1, h2, h3, Finset.sum_mul]
  exact Finset.sum_congr rfl fun k _ => by ring

/-! ## 3. `boxSlotSum` is linear in the one-body operator -/

/-- `boxSlotSum e ·` is additive in the one-body operator. -/
private theorem boxSlotSum_add {m d : ℕ} {e : Fin m → Sp → ℂ}
    (T₁ T₂ : (Fin m → ℝ) →ₗ[ℝ] (Fin m → ℝ)) (Θ : Xn d → ℂ) :
    boxSlotSum e (T₁ + T₂) Θ = boxSlotSum e T₁ Θ + boxSlotSum e T₂ Θ := by
  funext x
  simp only [boxSlotSum, LinearMap.add_apply, Pi.add_apply, Finset.sum_apply, Pi.smul_apply,
    add_smul, Finset.sum_add_distrib]

/-- `boxSlotSum e ·` is `ℝ`-homogeneous in the one-body operator. -/
private theorem boxSlotSum_smul {m d : ℕ} {e : Fin m → Sp → ℂ} (r : ℝ)
    (T : (Fin m → ℝ) →ₗ[ℝ] (Fin m → ℝ)) (Θ : Xn d → ℂ) :
    boxSlotSum e (r • T) Θ = r • boxSlotSum e T Θ := by
  funext x
  simp only [boxSlotSum, LinearMap.smul_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    mul_smul, ← Finset.smul_sum]

/-- `boxSlotSum e ·` is linear over a finite sum of one-body operators. -/
private theorem boxSlotSum_finset_smul_sum {m d : ℕ} {e : Fin m → Sp → ℂ} {κ : Type*}
    (s : Finset κ) (c : κ → ℝ) (T : κ → (Fin m → ℝ) →ₗ[ℝ] (Fin m → ℝ)) (Θ : Xn d → ℂ) :
    boxSlotSum e (∑ k ∈ s, c k • T k) Θ = ∑ k ∈ s, c k • boxSlotSum e (T k) Θ := by
  classical
  induction s using Finset.induction with
  | empty =>
      have h0 : (∑ k ∈ (∅ : Finset κ), c k • T k) = 0 := Finset.sum_empty
      rw [h0, Finset.sum_empty]
      simp [boxSlotSum]
  | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, boxSlotSum_add, boxSlotSum_smul, ih]

/-! ## 4. Linearity of `boxSlotSum` in the *state*, at the weak mode bundle

`Work.MB.boxSlotSum_bdd` supplies the linearity of `boxSlotSum e T` in the state at the weak mode
bundle, but with the index type of the finite sum restricted to `Type` (universe `0`).  The two-term
cases are enough to run the general `Finset` induction over an index type in *any* universe, which
is what the collapse of the two mode sums needs (`Mode` is universe-polymorphic). -/

/-- Measurable, everywhere bounded box states. -/
private def BoxGood {d : ℕ} (Φ : Xn d → ℂ) : Prop :=
  Measurable Φ ∧ ∃ C : ℝ, ∀ x, ‖Φ x‖ ≤ C

private theorem BoxGood.zero {d : ℕ} : BoxGood (0 : Xn d → ℂ) :=
  ⟨measurable_zero, 0, fun x => by simp⟩

private theorem BoxGood.smul {d : ℕ} (c : ℂ) {Φ : Xn d → ℂ} (h : BoxGood Φ) :
    BoxGood (c • Φ) := by
  obtain ⟨C, hC⟩ := h.2
  exact ⟨h.1.const_smul c, ‖c‖ * C, fun x => by
    rw [Pi.smul_apply, norm_smul]
    exact mul_le_mul_of_nonneg_left (hC x) (norm_nonneg _)⟩

private theorem BoxGood.add {d : ℕ} {Φ Ψ : Xn d → ℂ} (hΦ : BoxGood Φ) (hΨ : BoxGood Ψ) :
    BoxGood (Φ + Ψ) := by
  obtain ⟨C₁, h₁⟩ := hΦ.2
  obtain ⟨C₂, h₂⟩ := hΨ.2
  exact ⟨hΦ.1.add hΨ.1, C₁ + C₂, fun x => by
    rw [Pi.add_apply]
    exact (norm_add_le _ _).trans (add_le_add (h₁ x) (h₂ x))⟩

private theorem BoxGood.finset_smul_sum {d : ℕ} {σ : Type*} [DecidableEq σ] (s : Finset σ)
    (c : σ → ℂ) {Ψ : σ → Xn d → ℂ} (h : ∀ k, BoxGood (Ψ k)) :
    BoxGood (∑ k ∈ s, c k • Ψ k) := by
  classical
  induction s using Finset.induction with
  | empty => simpa using (BoxGood.zero : BoxGood (0 : Xn d → ℂ))
  | insert a s ha ih =>
      rw [Finset.sum_insert ha]
      exact BoxGood.add (BoxGood.smul (c a) (h a)) ih

/-- `boxSlotSum e T` of the zero state is zero. -/
private theorem boxSlotSum_zero_box {m d : ℕ} {e : Fin m → Sp → ℂ}
    (T : (Fin m → ℝ) →ₗ[ℝ] (Fin m → ℝ)) :
    boxSlotSum e T (0 : Xn d → ℂ) = 0 := by
  funext x
  simp [boxSlotSum, boxSlotOf]

/-- Additivity of `boxSlotSum e T` in the state, at the weak mode bundle: the two-term case of
`Work.MB.boxSlotSum_bdd`'s linearity conjunct, taken at the (universe-`0`) index type `Fin 2`. -/
private theorem boxSlotSum_add_good {m d : ℕ} {ℓ : ℝ} {e : Fin m → Sp → ℂ}
    (hmeas : ∀ l, Measurable (e l)) (hbdd : ∀ l, ∃ C : ℝ, ∀ x, ‖e l x‖ ≤ C)
    (hsupp : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ)
    (T : (Fin m → ℝ) →ₗ[ℝ] (Fin m → ℝ)) {Φ Ψ : Xn d → ℂ} (hΦ : BoxGood Φ)
    (hΨ : BoxGood Ψ) :
    boxSlotSum e T (Φ + Ψ) = boxSlotSum e T Φ + boxSlotSum e T Ψ := by
  have h := (Work.MB.boxSlotSum_bdd (d := d) hmeas hbdd hsupp T).1 (κ := Fin 2)
    (Finset.univ : Finset (Fin 2)) (fun _ : Fin 2 => (1 : ℂ))
    (fun i : Fin 2 => if i = 0 then Φ else Ψ)
    (fun i => by
      by_cases hi : i = 0
      · simp only [hi, if_true]; exact hΦ.1
      · simp only [hi, if_false]; exact hΨ.1)
    (fun i => by
      by_cases hi : i = 0
      · simp only [hi, if_true]; exact hΦ.2
      · simp only [hi, if_false]; exact hΨ.2)
  have h1 : (fun x : Xn d => ∑ i : Fin 2, (1 : ℂ) • (if i = 0 then Φ else Ψ) x)
      = Φ + Ψ := by
    funext x
    simp
  have h2 : (fun x : Xn d => ∑ i : Fin 2, (1 : ℂ) •
        boxSlotSum e T (if i = 0 then Φ else Ψ) x)
      = boxSlotSum e T Φ + boxSlotSum e T Ψ := by
    funext x
    simp
  rw [← h1, h, h2]

/-- `ℂ`-homogeneity of `boxSlotSum e T` in the state, at the weak mode bundle. -/
private theorem boxSlotSum_smul_good {m d : ℕ} {ℓ : ℝ} {e : Fin m → Sp → ℂ}
    (hmeas : ∀ l, Measurable (e l)) (hbdd : ∀ l, ∃ C : ℝ, ∀ x, ‖e l x‖ ≤ C)
    (hsupp : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ)
    (T : (Fin m → ℝ) →ₗ[ℝ] (Fin m → ℝ)) (c : ℂ) {Φ : Xn d → ℂ} (hΦ : BoxGood Φ) :
    boxSlotSum e T (c • Φ) = c • boxSlotSum e T Φ := by
  have h := (Work.MB.boxSlotSum_bdd (d := d) hmeas hbdd hsupp T).1 (κ := Fin 2)
    (Finset.univ : Finset (Fin 2)) (fun i : Fin 2 => if i = 0 then c else 0)
    (fun _ : Fin 2 => Φ) (fun _ => hΦ.1) (fun _ => hΦ.2)
  have h1 : (fun x : Xn d => ∑ i : Fin 2, (if i = 0 then c else 0) • Φ x) = c • Φ := by
    funext x
    simp
  have h2 : (fun x : Xn d => ∑ i : Fin 2, (if i = 0 then c else 0) •
        boxSlotSum e T Φ x) = c • boxSlotSum e T Φ := by
    funext x
    simp
  rw [← h1, h, h2]

/-- Linearity of `boxSlotSum e T` in the state over an arbitrary finite sum, at the weak mode
bundle and at an index type in any universe. -/
private theorem boxSlotSum_finset_sum_good {m d : ℕ} {ℓ : ℝ} {e : Fin m → Sp → ℂ}
    (hmeas : ∀ l, Measurable (e l)) (hbdd : ∀ l, ∃ C : ℝ, ∀ x, ‖e l x‖ ≤ C)
    (hsupp : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ)
    (T : (Fin m → ℝ) →ₗ[ℝ] (Fin m → ℝ)) {σ : Type*} [DecidableEq σ] (s : Finset σ)
    (c : σ → ℂ) (Ψ : σ → Xn d → ℂ) (hΨ : ∀ k, BoxGood (Ψ k)) :
    boxSlotSum e T (∑ k ∈ s, c k • Ψ k) = ∑ k ∈ s, c k • boxSlotSum e T (Ψ k) := by
  classical
  induction s using Finset.induction with
  | empty =>
      rw [Finset.sum_empty, Finset.sum_empty]
      exact boxSlotSum_zero_box T
  | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha,
        boxSlotSum_add_good hmeas hbdd hsupp T (BoxGood.smul (c a) (hΨ a))
          (BoxGood.finset_smul_sum s c hΨ),
        boxSlotSum_smul_good hmeas hbdd hsupp T (c a) (hΨ a), ih]

/-- The same with **real** scalars (the form in which the `hatChi`-prefactors occur). -/
private theorem boxSlotSum_finset_sum_real {m d : ℕ} {ℓ : ℝ} {e : Fin m → Sp → ℂ}
    (hmeas : ∀ l, Measurable (e l)) (hbdd : ∀ l, ∃ C : ℝ, ∀ x, ‖e l x‖ ≤ C)
    (hsupp : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ)
    (T : (Fin m → ℝ) →ₗ[ℝ] (Fin m → ℝ)) {σ : Type*} [DecidableEq σ] (s : Finset σ)
    (c : σ → ℝ) (Ψ : σ → Xn d → ℂ) (hΨ : ∀ k, BoxGood (Ψ k)) :
    boxSlotSum e T (∑ k ∈ s, c k • Ψ k) = ∑ k ∈ s, c k • boxSlotSum e T (Ψ k) := by
  have h1 : (∑ k ∈ s, c k • Ψ k) = ∑ k ∈ s, ((c k : ℂ)) • Ψ k := by
    refine Finset.sum_congr rfl fun k _ => ?_
    funext x
    rw [Pi.smul_apply, Pi.smul_apply, real_smul_eq_complex_smul]
  have h2 : (∑ k ∈ s, c k • boxSlotSum e T (Ψ k))
      = ∑ k ∈ s, ((c k : ℂ)) • boxSlotSum e T (Ψ k) := by
    refine Finset.sum_congr rfl fun k _ => ?_
    funext x
    rw [Pi.smul_apply, Pi.smul_apply, real_smul_eq_complex_smul]
  rw [h1, h2, boxSlotSum_finset_sum_good hmeas hbdd hsupp T s (fun k => (c k : ℂ)) Ψ hΨ]

/-! ## 5. The collapse of the two mode sums -/

theorem potChiLin_eq_summed_good {n m : ℕ} [NeZero m] {ℓ : ℝ}
    {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
    {e : Fin m → Work.BoseDict.Sp → ℂ}
    (he : ∀ l, Measurable (e l)) (hb : ∀ l, ∃ C : ℝ, ∀ x, ‖e l x‖ ≤ C)
    (hs : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ)
    (f g : Mode → Fin m → ℝ) (E : Work.BoseB7.Q3Env Mode)
    {Θ : Work.BoseDict.Xn n → ℂ} (hΘm : Measurable Θ)
    (hΘb : ∃ C : ℝ, ∀ x, ‖Θ x‖ ≤ C)
    (hΘs : Function.support Θ ⊆ Submission.BoseGases.abox n ℓ) :
    Work.BoseBoxFock.potChiLin (ι := Fin n) (fun T => Work.BoseDict.boxSlotSum e T) f g E Θ
      = Work.BoseBoxFock.potChiLinSummed (ι := Fin n)
          (fun T => Work.BoseDict.boxSlotSum e T)
          (∑ k : Mode, E.hatChi k • (f k))
          (∑ s ∈ Work.BoseB7.excited Mode, E.hatChiSq s • (g s)) E Θ := by
  classical
  -- ## the collapse of `boxSlotSum e ·` in the one-body argument, at the state `Θ`
  have hP : boxSlotSum e (rankOnePair (∑ k : Mode, E.hatChi k • (f k)) (evec0 m)) Θ
      = ∑ k : Mode, E.hatChi k • boxSlotSum e (rankOnePair (f k) (evec0 m)) Θ := by
    rw [rankOnePair_finset_sum_left, boxSlotSum_finset_smul_sum]
  have hQ : boxSlotSum e (rankOnePair (evec0 m) (∑ k : Mode, E.hatChi k • (f k))) Θ
      = ∑ k : Mode, E.hatChi k • boxSlotSum e (rankOnePair (evec0 m) (f k)) Θ := by
    rw [rankOnePair_finset_sum_right, boxSlotSum_finset_smul_sum]
  have hP' : boxSlotSum e
        (rankOnePair (∑ s ∈ Work.BoseB7.excited Mode, E.hatChiSq s • (g s)) (evec0 m)) Θ
      = ∑ s ∈ Work.BoseB7.excited Mode, E.hatChiSq s •
          boxSlotSum e (rankOnePair (g s) (evec0 m)) Θ := by
    rw [rankOnePair_finset_sum_left, boxSlotSum_finset_smul_sum]
  have hQ' : boxSlotSum e
        (rankOnePair (evec0 m) (∑ s ∈ Work.BoseB7.excited Mode, E.hatChiSq s • (g s))) Θ
      = ∑ s ∈ Work.BoseB7.excited Mode, E.hatChiSq s •
          boxSlotSum e (rankOnePair (evec0 m) (g s)) Θ := by
    rw [rankOnePair_finset_sum_right, boxSlotSum_finset_smul_sum]
  -- ## the regularity of the intermediate states
  have hreg : ∀ (v : Fin m → ℝ), BoxGood (boxSlotSum e (rankOnePair v (evec0 m)) Θ) := by
    intro v
    obtain ⟨hm, ⟨C, -, hC⟩, -⟩ :=
      (Work.MB.boxSlotSum_bdd (d := n) he hb hs (rankOnePair v (evec0 m))).2 Θ hΘm hΘb
    exact ⟨hm, C, hC⟩
  -- ## the collapse of the two-letter products (state linearity of `boxSlotSum e (|e₀⟩⟨e₀|)`)
  have hAP : boxSlotSum e (rankOne (evec0 m))
        (boxSlotSum e (rankOnePair (∑ k : Mode, E.hatChi k • (f k)) (evec0 m)) Θ)
      = ∑ k : Mode, E.hatChi k • boxSlotSum e (rankOne (evec0 m))
          (boxSlotSum e (rankOnePair (f k) (evec0 m)) Θ) := by
    rw [hP]
    exact boxSlotSum_finset_sum_real he hb hs (rankOne (evec0 m)) Finset.univ
      (fun k => E.hatChi k) (fun k => boxSlotSum e (rankOnePair (f k) (evec0 m)) Θ)
      (fun k => hreg (f k))
  have hQA : boxSlotSum e (rankOnePair (evec0 m) (∑ k : Mode, E.hatChi k • (f k)))
        (boxSlotSum e (rankOne (evec0 m)) Θ)
      = ∑ k : Mode, E.hatChi k • boxSlotSum e (rankOnePair (evec0 m) (f k))
          (boxSlotSum e (rankOne (evec0 m)) Θ) := by
    rw [rankOnePair_finset_sum_right, boxSlotSum_finset_smul_sum]
  have hAP' : boxSlotSum e (rankOne (evec0 m))
        (boxSlotSum e
          (rankOnePair (∑ s ∈ Work.BoseB7.excited Mode, E.hatChiSq s • (g s)) (evec0 m)) Θ)
      = ∑ s ∈ Work.BoseB7.excited Mode, E.hatChiSq s • boxSlotSum e (rankOne (evec0 m))
          (boxSlotSum e (rankOnePair (g s) (evec0 m)) Θ) := by
    rw [hP']
    exact boxSlotSum_finset_sum_real he hb hs (rankOne (evec0 m)) (Work.BoseB7.excited Mode)
      (fun s => E.hatChiSq s) (fun s => boxSlotSum e (rankOnePair (g s) (evec0 m)) Θ)
      (fun s => hreg (g s))
  have hQA' : boxSlotSum e
          (rankOnePair (evec0 m) (∑ s ∈ Work.BoseB7.excited Mode, E.hatChiSq s • (g s)))
        (boxSlotSum e (rankOne (evec0 m)) Θ)
      = ∑ s ∈ Work.BoseB7.excited Mode, E.hatChiSq s •
          boxSlotSum e (rankOnePair (evec0 m) (g s)) (boxSlotSum e (rankOne (evec0 m)) Θ) := by
    rw [rankOnePair_finset_sum_right, boxSlotSum_finset_smul_sum]
  -- ## assemble
  simp only [potChiLin, potChiLinSummed]
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, Function.comp_apply, Finset.sum_apply]
  rw [hAP, hQA, hAP', hQA', hP, hQ]
  conv_rhs => rw [smul_finset_sum_smul, smul_finset_sum_smul, smul_finset_sum_smul,
    smul_finset_sum_smul, smul_finset_sum_smul, smul_finset_sum_smul]
  simp only [smul_add, smul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  abel

end Work.BoseBoxFock
