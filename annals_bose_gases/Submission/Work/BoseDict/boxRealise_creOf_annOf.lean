import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Data.Finsupp.Pointwise
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseDictC.integrable_conj_etaOf_modeProd_cons
import Submission.Work.BoseDictC.integral_conj_etaOf_modeProd_cons
import Submission.Work.BoseDictC.mfac_add_single
import Submission.Work.BoseDictC.mfac_sub_single_mul
import Submission.Work.BoseDictC.sum_star_modeProd_succAbove
import Submission.Work.BoseDictC.sum_sub_single_of_ne_zero
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseDict.boxRealise_creOf_annOf`

The box realisation intertwines the model's composed operator `creOf w ∘ annOf v` with the
box's composed operator `boxCreOf w ∘ boxAnnOf v`:

`boxRealise e (d+1) (creOf m w (annOf m v Ψ)) = boxCreOf e w d (boxAnnOf e v d (boxRealise e (d+1) Ψ))`.

The proof factors the composite into its two halves, proved separately here from the
delegated mode-product cores:

* `boxRealise_annOf_aux` — `boxRealise e d ∘ annOf m w = boxAnnOf e w d ∘ boxRealise e (d+1)`
  (the annihilation half), built by `Finsupp.induction_linear` from the single-monomial
  identity `boxRealise_annOf_single` (whose content is the integral identity
  `Work.BoseDictC.integral_conj_etaOf_modeProd_cons` plus the integrability input
  `Work.BoseDictC.integrable_conj_etaOf_modeProd_cons`);
* `boxCreOf_boxRealise` — `boxCreOf e w d ∘ boxRealise e d = boxRealise e (d+1) ∘ creOf m w`
  (the creation half), whose single-monomial content is the combinatorial identity
  `Work.BoseDictC.sum_star_modeProd_succAbove`.

The two halves are then composed by a two-step rewrite.
-/

open scoped BigOperators
open MeasureTheory

namespace Work.BoseDict

/- Auxiliary declarations for `boxRealise_creOf_annOf`, kept in their own namespace so that
they cannot clash with the (independent) dictionary files being written in parallel. -/
namespace CreOfAnnAux

/-- ℝ-scalar multiplication on ℂ is complex multiplication. -/
lemma real_smul_complex (r : ℝ) (z : ℂ) : r • z = (r : ℂ) * z := by
  rw [Algebra.smul_def]; rfl

/-- The normalisation coefficient of `boxRealise`: `γ ↦ [|γ| = d] · γ!/√(d!)`. -/
noncomputable def mcoef {m : ℕ} (d : ℕ) (γ : Fin m →₀ ℕ) : ℝ :=
  if γ.sum (fun _ k => k) = d then Work.BoseB4.mfac γ / Real.sqrt (d.factorial : ℝ) else 0

/-- `boxRealise` on the Finsupp basis. -/
lemma boxRealise_eq_sum {m d : ℕ} (e : Fin m → Sp → ℂ) (Ψ : Work.BoseB4.RealFock m) :
    boxRealise e d Ψ = ∑ α ∈ Ψ.support,
      (Ψ α * (if α.sum (fun _ k => k) = d then Work.BoseB4.mfac α / Real.sqrt (d.factorial : ℝ) else 0)) • modeProd e d α := by
  have h1 : Ψ = ∑ α ∈ Ψ.support, Finsupp.single α (Ψ α) := (Finsupp.sum_single (f := Ψ)).symm
  conv_lhs => rw [h1]
  rw [map_sum]
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [← Finsupp.smul_single_one, map_smul, boxRealise_single, smul_smul]

/-- `boxRealise` of a single monomial. -/
lemma boxRealise_single_eq {m d : ℕ} (e : Fin m → Sp → ℂ) (γ : Fin m →₀ ℕ) (b : ℝ) :
    boxRealise e d (Finsupp.single γ b) = (b * mcoef d γ) • modeProd e d γ := by
  rw [← Finsupp.smul_single_one, map_smul, boxRealise_single, smul_smul]
  rfl

/-- `cre` of a single monomial. -/
lemma cre_single {m : ℕ} (l : Fin m) (α : Fin m →₀ ℕ) (b : ℝ) :
    Work.BoseB4.cre m l (Finsupp.single α b) = Finsupp.single (α + Work.BoseB4.e m l) b := by
  simp [Work.BoseB4.cre, Finsupp.lsum_single]

/-- `ann` of a single monomial. -/
lemma ann_single {m : ℕ} (l : Fin m) (α : Fin m →₀ ℕ) (b : ℝ) :
    Work.BoseB4.ann m l (Finsupp.single α b)
      = b • ((α l : ℝ) • Finsupp.single (α - Work.BoseB4.e m l) 1) := by
  simp [Work.BoseB4.ann, Finsupp.lsum_single, LinearMap.toSpanSingleton_apply]

/-- Degree of `β + e_l`. -/
lemma sum_add_e {m : ℕ} (β : Fin m →₀ ℕ) (l : Fin m) :
    (β + Work.BoseB4.e m l).sum (fun _ j => j) = β.sum (fun _ j => j) + 1 := by
  rw [Finsupp.sum_add_index (h := fun _ j => j)]
  · simp [Work.BoseB4.e, Finsupp.sum_single_index]
  · intro a _; rfl
  · intro a _ b₁ b₂; rfl

/-- `√((d+1)!) = √(d!)·√(d+1)`. -/
lemma sqrt_factorial_succ (d : ℕ) :
    Real.sqrt ((d + 1).factorial : ℝ) = Real.sqrt (d.factorial : ℝ) * Real.sqrt ((d : ℝ) + 1) := by
  have h : ((d + 1).factorial : ℝ) = (d.factorial : ℝ) * ((d : ℝ) + 1) := by
    rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
    ring
  rw [h, Real.sqrt_mul (Nat.cast_nonneg _)]

/-- `boxCreOf` is additive in the state. -/
lemma boxCreOf_add {m d : ℕ} (e : Fin m → Sp → ℂ) (w : Fin m → ℝ) (Θ Θ' : Xn d → ℂ) :
    boxCreOf e w d (Θ + Θ') = boxCreOf e w d Θ + boxCreOf e w d Θ' := by
  funext x
  simp only [boxCreOf, Pi.add_apply]
  have h : (∑ j : Fin (d + 1), etaOf e w (x j)
        * (Θ (fun i : Fin d => x (Fin.succAbove j i))
            + Θ' (fun i : Fin d => x (Fin.succAbove j i))))
      = (∑ j : Fin (d + 1), etaOf e w (x j) * Θ (fun i : Fin d => x (Fin.succAbove j i)))
        + ∑ j : Fin (d + 1), etaOf e w (x j) * Θ' (fun i : Fin d => x (Fin.succAbove j i)) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j _ => mul_add _ _ _
  rw [h, mul_add]

/-- `boxCreOf` is homogeneous in the state (ℝ-scalars). -/
lemma boxCreOf_smul {m d : ℕ} (e : Fin m → Sp → ℂ) (w : Fin m → ℝ) (r : ℝ) (Θ : Xn d → ℂ) :
    boxCreOf e w d (r • Θ) = r • boxCreOf e w d Θ := by
  funext x
  simp only [boxCreOf, Pi.smul_apply]
  have h : (∑ j : Fin (d + 1), etaOf e w (x j) * (r • Θ (fun i : Fin d => x (Fin.succAbove j i))))
      = (r : ℂ) * ∑ j : Fin (d + 1), etaOf e w (x j) * Θ (fun i : Fin d => x (Fin.succAbove j i)) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [real_smul_complex]
    ring
  rw [h, real_smul_complex]
  ring

/-- The coefficient identity behind the creation superposition identity. -/
lemma coeff_cre {m : ℕ} (d : ℕ) (β : Fin m →₀ ℕ) (l : Fin m) :
    mcoef d β * (((β l : ℝ) + 1) / Real.sqrt ((d : ℝ) + 1)) = mcoef (d + 1) (β + Work.BoseB4.e m l) := by
  have h9 : Work.BoseB4.mfac (β + Work.BoseB4.e m l) = ((β l : ℝ) + 1) * Work.BoseB4.mfac β :=
    Work.BoseDictC.mfac_add_single β l
  simp only [mcoef]
  by_cases h : β.sum (fun _ k => k) = d
  · have h1 : (β + Work.BoseB4.e m l).sum (fun _ k => k) = d + 1 := by rw [sum_add_e, h]
    rw [if_pos h, if_pos h1, h9, sqrt_factorial_succ]
    rw [div_mul_div_comm]
    ring
  · have h1 : (β + Work.BoseB4.e m l).sum (fun _ k => k) ≠ d + 1 := by
      rw [sum_add_e]
      intro hh
      exact h (Nat.add_right_cancel hh)
    rw [if_neg h, if_neg h1, zero_mul]

lemma boxCreOf_zero {m d : ℕ} (e : Fin m → Sp → ℂ) (w : Fin m → ℝ) :
    boxCreOf e w d (0 : Xn d → ℂ) = 0 := by
  funext x; simp [boxCreOf]

/-- The single-monomial creation identity. -/
theorem boxCreOf_boxRealise_single {m d : ℕ} (e : Fin m → Sp → ℂ) (w : Fin m → ℝ)
    (β : Fin m →₀ ℕ) (b : ℝ) :
    boxCreOf e w d (boxRealise e d (Finsupp.single β b))
      = boxRealise e (d + 1) (Work.BoseB4.creOf m w (Finsupp.single β b)) := by
  funext x
  rw [boxRealise_single_eq, boxCreOf_smul]
  have hcre : Work.BoseB4.creOf m w (Finsupp.single β b)
      = ∑ l : Fin m, (w l) • Finsupp.single (β + Work.BoseB4.e m l) b := by
    rw [Work.BoseB4.creOf]
    simp only [LinearMap.sum_apply, LinearMap.smul_apply, cre_single]
  rw [hcre, map_sum]
  simp only [boxCreOf, Pi.smul_apply, Finset.sum_apply, real_smul_complex, map_smul,
    boxRealise_single_eq]
  have hS : (∑ j : Fin (d + 1), etaOf e w (x j) * modeProd e d β (fun i : Fin d => x (Fin.succAbove j i)))
      = ∑ l : Fin m, (w l : ℂ) * (((β l : ℝ) + 1 : ℂ) * modeProd e (d + 1) (β + Work.BoseB4.e m l) x) := by
    have h1 : ∀ j : Fin (d + 1),
        etaOf e w (x j) * modeProd e d β (fun i : Fin d => x (Fin.succAbove j i))
        = ∑ l : Fin m, (w l : ℂ) * (e l (x j)
            * modeProd e d β (fun i : Fin d => x (Fin.succAbove j i))) := by
      intro j
      rw [etaOf, Finset.sum_mul]
      exact Finset.sum_congr rfl fun l _ => by ring
    rw [Finset.sum_congr rfl (fun j _ => h1 j), Finset.sum_comm]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [← Work.BoseDictC.sum_star_modeProd_succAbove l β x, Finset.mul_sum]
  rw [hS, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [← coeff_cre d β l]
  push_cast
  ring

/-- The creation superposition identity (no degree hypothesis needed). -/
theorem boxCreOf_boxRealise {m d : ℕ} (e : Fin m → Sp → ℂ) (w : Fin m → ℝ)
    (Ψ : Work.BoseB4.RealFock m) :
    boxCreOf e w d (boxRealise e d Ψ) = boxRealise e (d + 1) (Work.BoseB4.creOf m w Ψ) := by
  induction Ψ using Finsupp.induction_linear with
  | zero => simp only [map_zero, boxCreOf_zero]
  | add f g hf hg =>
    calc boxCreOf e w d (boxRealise e d (f + g))
        = boxCreOf e w d (boxRealise e d f) + boxCreOf e w d (boxRealise e d g) := by
          rw [map_add, boxCreOf_add]
      _ = boxRealise e (d + 1) (Work.BoseB4.creOf m w f)
            + boxRealise e (d + 1) (Work.BoseB4.creOf m w g) := by rw [hf, hg]
      _ = boxRealise e (d + 1) (Work.BoseB4.creOf m w (f + g)) := by
          rw [← map_add, ← map_add]
  | single β b => exact boxCreOf_boxRealise_single e w β b

/-! ### Part A: the annihilation superposition identity -/

/-- Wrapper: degree of `α - e_k`. -/
lemma sum_sub_e_of_ne_zero {m : ℕ} (α : Fin m →₀ ℕ) (k : Fin m) (h : α k ≠ 0) :
    (α - Work.BoseB4.e m k).sum (fun _ j => j) = α.sum (fun _ j => j) - 1 :=
  Work.BoseDictC.sum_sub_single_of_ne_zero α k h

/-- Wrapper: `mfac` after removing one `k`. -/
lemma mfac_sub_e_mul {m : ℕ} (α : Fin m →₀ ℕ) (k : Fin m) (h : α k ≠ 0) :
    (α k : ℝ) * Work.BoseB4.mfac (α - Work.BoseB4.e m k) = Work.BoseB4.mfac α :=
  Work.BoseDictC.mfac_sub_single_mul α k h

/-- Degree of `α - e_k` inverted: `|α| = |α - e_k| + 1`. -/
lemma le_sum_of_ne_zero {m : ℕ} (α : Fin m →₀ ℕ) (k : Fin m) (h : α k ≠ 0) :
    α.sum (fun _ j => j) = (α - Work.BoseB4.e m k).sum (fun _ j => j) + 1 := by
  have hpos : 0 < α.sum (fun _ j => j) := by
    have hle := Finsupp.single_eval_le_sum α (g := fun n : ℕ => n) rfl
      (fun _ => Nat.zero_le _) k
    exact lt_of_lt_of_le (Nat.pos_of_ne_zero h) hle
  have h2 := sum_sub_e_of_ne_zero α k h
  omega

lemma sub_e_of_apply_eq_zero {m : ℕ} {α : Fin m →₀ ℕ} {l : Fin m} (h : α l = 0) :
    α - Work.BoseB4.e m l = α := by
  ext i
  rcases eq_or_ne i l with rfl | hne
  · simp [h, Work.BoseB4.e]
  · simp [Work.BoseB4.e, hne]

lemma mcoef_of_sum {m : ℕ} {d : ℕ} {γ : Fin m →₀ ℕ} (h : γ.sum (fun _ k => k) = d) :
    mcoef d γ = Work.BoseB4.mfac γ / Real.sqrt (d.factorial : ℝ) := by
  simp only [mcoef]; rw [if_pos h]

lemma mcoef_of_ne_sum {m : ℕ} {d : ℕ} {γ : Fin m →₀ ℕ} (h : γ.sum (fun _ k => k) ≠ d) :
    mcoef d γ = 0 := by
  simp only [mcoef]; rw [if_neg h]

/-- `annOf` on a single monomial. -/
lemma annOf_single {m : ℕ} (w : Fin m → ℝ) (β : Fin m →₀ ℕ) (b : ℝ) :
    Work.BoseB4.annOf m w (Finsupp.single β b)
      = ∑ l : Fin m, (w l * b * (β l : ℝ)) • Finsupp.single (β - Work.BoseB4.e m l) 1 := by
  rw [Work.BoseB4.annOf]
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, ann_single, smul_smul]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [← mul_assoc]

lemma boxAnnOf_zero {m d : ℕ} (e : Fin m → Sp → ℂ) (w : Fin m → ℝ) :
    boxAnnOf e w d (0 : Xn (d + 1) → ℂ) = 0 := by
  funext y; simp [boxAnnOf]

/-- `boxAnnOf` is homogeneous in the state (ℝ-scalars). -/
lemma boxAnnOf_smul {m d : ℕ} (e : Fin m → Sp → ℂ) (w : Fin m → ℝ) (r : ℝ)
    (Θ : Xn (d + 1) → ℂ) :
    boxAnnOf e w d (r • Θ) = r • boxAnnOf e w d Θ := by
  funext y
  simp only [boxAnnOf, Pi.smul_apply]
  have h1 : (fun z : Sp => (starRingEnd ℂ) (etaOf e w z) * (r • Θ (Fin.cons z y)))
      = fun z : Sp => (r : ℂ) * ((starRingEnd ℂ) (etaOf e w z) * Θ (Fin.cons z y)) := by
    funext z; rw [real_smul_complex]; ring
  rw [h1, MeasureTheory.integral_const_mul, real_smul_complex]
  ring

/-- `boxAnnOf` is additive in the state, given integrability of both summands. -/
lemma boxAnnOf_add {m d : ℕ} (e : Fin m → Sp → ℂ) (w : Fin m → ℝ) (Θ Θ' : Xn (d + 1) → ℂ)
    (y : Xn d)
    (h : MeasureTheory.Integrable (fun z : Sp => (starRingEnd ℂ) (etaOf e w z) * Θ (Fin.cons z y)))
    (h' : MeasureTheory.Integrable
      (fun z : Sp => (starRingEnd ℂ) (etaOf e w z) * Θ' (Fin.cons z y))) :
    boxAnnOf e w d (Θ + Θ') y = boxAnnOf e w d Θ y + boxAnnOf e w d Θ' y := by
  simp only [boxAnnOf, Pi.add_apply]
  have h1 : (fun z : Sp => (starRingEnd ℂ) (etaOf e w z)
        * (Θ (Fin.cons z y) + Θ' (Fin.cons z y)))
      = fun z : Sp => (starRingEnd ℂ) (etaOf e w z) * Θ (Fin.cons z y)
          + (starRingEnd ℂ) (etaOf e w z) * Θ' (Fin.cons z y) := by
    funext z; ring
  rw [h1, MeasureTheory.integral_add h h', mul_add]

/-- Integrability of `conj(η_w)·boxRealise` along the `cons` slice. -/
lemma integrable_conj_etaOf_boxRealise {m d : ℕ} {ℓ : ℝ} {e : Fin m → Sp → ℂ}
    (hbdd : ∀ l, MeasureTheory.MemLp (e l) ⊤)
    (hsupp : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ)
    (w : Fin m → ℝ) (Ψ : Work.BoseB4.RealFock m) (y : Xn d) :
    MeasureTheory.Integrable
      (fun z : Sp => (starRingEnd ℂ) (etaOf e w z) * boxRealise e (d + 1) Ψ (Fin.cons z y)) := by
  induction Ψ using Finsupp.induction_linear with
  | zero =>
      have h0 : (fun z : Sp => (starRingEnd ℂ) (etaOf e w z)
            * boxRealise e (d + 1) (0 : Work.BoseB4.RealFock m) (Fin.cons z y))
          = fun _ : Sp => 0 := by
        funext z; simp
      rw [h0]; exact integrable_zero _ _ _
  | add f g hf hg =>
      rw [map_add]
      have h1 : (fun z : Sp => (starRingEnd ℂ) (etaOf e w z)
            * ((boxRealise e (d + 1) f + boxRealise e (d + 1) g) (Fin.cons z y)))
          = fun z : Sp => (starRingEnd ℂ) (etaOf e w z) * boxRealise e (d + 1) f (Fin.cons z y)
              + (starRingEnd ℂ) (etaOf e w z) * boxRealise e (d + 1) g (Fin.cons z y) := by
        funext z; rw [Pi.add_apply, mul_add]
      rw [h1]; exact hf.add hg
  | single β b =>
      rw [boxRealise_single_eq]
      by_cases hβ : β.sum (fun _ k => k) = d + 1
      · have h4 := Work.BoseDictC.integrable_conj_etaOf_modeProd_cons (d := d) hbdd hsupp w hβ y
        have h1 : (fun z : Sp => (starRingEnd ℂ) (etaOf e w z)
              * ((b * mcoef (d + 1) β) • modeProd e (d + 1) β) (Fin.cons z y))
            = fun z : Sp => ((b * mcoef (d + 1) β : ℝ) : ℂ)
                * ((starRingEnd ℂ) (etaOf e w z) * modeProd e (d + 1) β (Fin.cons z y)) := by
          funext z
          rw [Pi.smul_apply, real_smul_complex]
          ring
        rw [h1]; exact h4.const_mul _
      · rw [mcoef_of_ne_sum hβ]
        have h1 : (fun z : Sp => (starRingEnd ℂ) (etaOf e w z)
              * ((b * 0) • modeProd e (d + 1) β) (Fin.cons z y)) = fun _ : Sp => 0 := by
          funext z; simp
        rw [h1]; exact integrable_zero _ _ _

/-- The coefficient identity behind the annihilation superposition identity. -/
lemma coeff_ann {m : ℕ} (d : ℕ) (β : Fin m →₀ ℕ) (l : Fin m)
    (hβ : β.sum (fun _ k => k) = d + 1) (hl : β l ≠ 0) :
    (β l : ℝ) * mcoef d (β - Work.BoseB4.e m l)
      = mcoef (d + 1) β * Real.sqrt ((d : ℝ) + 1) := by
  have h1 : (β - Work.BoseB4.e m l).sum (fun _ k => k) = d := by
    rw [sum_sub_e_of_ne_zero β l hl, hβ, Nat.add_sub_cancel]
  rw [mcoef_of_sum h1, mcoef_of_sum hβ, sqrt_factorial_succ, ← mfac_sub_e_mul β l hl]
  have hd0 : Real.sqrt (d.factorial : ℝ) ≠ 0 := by positivity
  have hd1 : Real.sqrt ((d : ℝ) + 1) ≠ 0 := by positivity
  field_simp

/-- The single-monomial annihilation identity. -/
theorem boxRealise_annOf_single {m d : ℕ} {ℓ : ℝ} {e : Fin m → Sp → ℂ}
    (he : ∀ l l', (∫ x : Sp, (starRingEnd ℂ) (e l x) * e l' x) = if l = l' then 1 else 0)
    (hbdd : ∀ l, MeasureTheory.MemLp (e l) ⊤)
    (hsupp : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ)
    (w : Fin m → ℝ) (β : Fin m →₀ ℕ) (b : ℝ) :
    boxRealise e d (Work.BoseB4.annOf m w (Finsupp.single β b))
      = boxAnnOf e w d (boxRealise e (d + 1) (Finsupp.single β b)) := by
  funext y
  rw [boxRealise_single_eq, boxAnnOf_smul, annOf_single]
  have hL : boxRealise e d (∑ l : Fin m,
        (w l * b * (β l : ℝ)) • Finsupp.single (β - Work.BoseB4.e m l) 1) y
      = ∑ l : Fin m, ((w l * b * (β l : ℝ)) * mcoef d (β - Work.BoseB4.e m l) : ℝ)
          * modeProd e d (β - Work.BoseB4.e m l) y := by
    rw [map_sum]
    simp only [map_smul, Finset.sum_apply, Pi.smul_apply, real_smul_complex, boxRealise_single_eq,
      one_mul]
    refine Finset.sum_congr rfl fun l _ => ?_
    push_cast
    ring
  rw [hL]
  by_cases hβ : β.sum (fun _ k => k) = d + 1
  · have hR : ((b * mcoef (d + 1) β) • boxAnnOf e w d (modeProd e (d + 1) β)) y
        = ∑ l : Fin m, ((b * mcoef (d + 1) β : ℝ) : ℂ)
            * ((Real.sqrt ((d : ℝ) + 1) : ℂ)
                * ((w l : ℂ) * modeProd e d (β - Work.BoseB4.e m l) y)) := by
      simp only [Pi.smul_apply, real_smul_complex, boxAnnOf]
      rw [Work.BoseDictC.integral_conj_etaOf_modeProd_cons (d := d) he hbdd hsupp w hβ y]
      rw [Finset.mul_sum, Finset.mul_sum]
    rw [hR]
    refine Finset.sum_congr rfl fun l _ => ?_
    by_cases hl : β l = 0
    · rw [sub_e_of_apply_eq_zero hl, Work.BoseDictC.modeProd_eq_zero_of_sum_ne β (by omega) y]
      simp
    · have hA : (w l * b * (β l : ℝ)) * mcoef d (β - Work.BoseB4.e m l)
          = (b * (mcoef (d + 1) β * Real.sqrt ((d : ℝ) + 1))) * w l := by
        rw [show (w l * b * (β l : ℝ)) * mcoef d (β - Work.BoseB4.e m l)
              = (b * w l) * ((β l : ℝ) * mcoef d (β - Work.BoseB4.e m l)) from by ring,
            coeff_ann d β l hβ hl]
        ring
      rw [hA]
      push_cast
      ring
  · have hz : ((b * mcoef (d + 1) β) • boxAnnOf e w d (modeProd e (d + 1) β)) y = 0 := by
      rw [mcoef_of_ne_sum hβ]; simp
    rw [hz]
    refine Finset.sum_eq_zero fun l _ => ?_
    by_cases hl : β l = 0
    · rw [hl]; simp
    · have h1 : (β - Work.BoseB4.e m l).sum (fun _ k => k) ≠ d := by
        have h2 := le_sum_of_ne_zero β l hl
        intro hcontra
        exact hβ (by omega)
      rw [mcoef_of_ne_sum h1]; simp

/-- The annihilation superposition identity (unconditional). -/
theorem boxRealise_annOf_aux {m d : ℕ} {ℓ : ℝ} {e : Fin m → Sp → ℂ}
    (he : ∀ l l', (∫ x : Sp, (starRingEnd ℂ) (e l x) * e l' x) = if l = l' then 1 else 0)
    (hbdd : ∀ l, MeasureTheory.MemLp (e l) ⊤)
    (hsupp : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ)
    (w : Fin m → ℝ) (Ψ : Work.BoseB4.RealFock m) :
    boxRealise e d (Work.BoseB4.annOf m w Ψ) = boxAnnOf e w d (boxRealise e (d + 1) Ψ) := by
  induction Ψ using Finsupp.induction_linear with
  | zero => simp only [map_zero, boxAnnOf_zero]
  | add f g hf hg =>
      rw [map_add, map_add, map_add, hf, hg]
      funext y
      rw [Pi.add_apply,
        boxAnnOf_add e w (boxRealise e (d + 1) f) (boxRealise e (d + 1) g) y
          (integrable_conj_etaOf_boxRealise hbdd hsupp w f y)
          (integrable_conj_etaOf_boxRealise hbdd hsupp w g y)]
  | single β b => exact boxRealise_annOf_single he hbdd hsupp w β b

end CreOfAnnAux

open CreOfAnnAux

/-- **The target lemma**: the box realisation intertwines the model's `creOf ∘ annOf`
with the box's `boxCreOf ∘ boxAnnOf`. -/
theorem boxRealise_creOf_annOf {m d : ℕ} {ℓ : ℝ} {e : Fin m → Work.BoseDict.Sp → ℂ}
    (he : ∀ l l', (∫ x : Work.BoseDict.Sp, (starRingEnd ℂ) (e l x) * e l' x) = if l = l' then 1 else 0)
    (hbdd : ∀ l, MeasureTheory.MemLp (e l) ⊤)
    (hsupp : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ)
    (w v : Fin m → ℝ) (Ψ : Work.BoseB4.RealFock m)
    (hΨ : ∀ α ∈ Ψ.support, α.sum (fun _ k => k) = d + 1) :
    Work.BoseDict.boxRealise e (d + 1) (Work.BoseB4.creOf m w (Work.BoseB4.annOf m v Ψ))
      = Work.BoseDict.boxCreOf e w d (Work.BoseDict.boxAnnOf e v d (Work.BoseDict.boxRealise e (d + 1) Ψ)) := by
  rw [← boxCreOf_boxRealise e w (Work.BoseB4.annOf m v Ψ),
    boxRealise_annOf_aux he hbdd hsupp v Ψ]

end Work.BoseDict
