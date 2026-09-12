import Submission.MinkBox
import Mathlib.MeasureTheory.Group.GeometryOfNumbers
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Algebra.Module.ZLattice.Covolume
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Vandermonde

noncomputable section

open Polynomial
open scoped Real BigOperators ENNReal Pointwise
open MeasureTheory MeasureTheory.Measure Set

/-!
# Volume of the weighted Vandermonde body

Self-contained module: proves `Submission.MinkVol.vol_weighted_vandermonde`:

for injective `α : Fin d → ℝ` and positive weights `v`, the open parallelepiped

    B := {x : Fin d → ℝ | ∀ k, |v k * (∑ j, x j * (α k)^j)| < 1}

has real Lebesgue measure `(2:ℝ)^d / MinkBox.Dval d α v` where
`Dval d α v = (∏ k, v k) * (∏_{i<j} |α i − α j|)` (see `Submission.MinkBox`).

## Proof plan
* Model `E = Fin d → ℝ` with volume.
* `T : E →ₗ[ℝ] E`, `(T x) k := v k * ∑ j, x j * (α k) ^ j.val`, is the linear map with
  matrix `A k j = v k * (α k) ^ j.val` w.r.t. the standard basis `Pi.basisFun ℝ (Fin d)`.
* `B = T ⁻¹' {y | ∀ k, |y k| < 1}` (the preimage of the open cube).
* `LinearMap.det T = A.det` (w.r.t. the standard basis) and `A.det = (∏ k, v k) *
  (∏_{i<j} (α j − α i))` (Vandermonde, `Matrix.det_vandermonde` or similar in
  `Mathlib.LinearAlgebra.Vandermonde`), hence `|A.det| = Dval d α v` and `A.det ≠ 0`
  (use injectivity of α and positivity of v: `Dval > 0`).
* `T` is therefore invertible; use the Haar measure lemma
  `addHaar_preimage_linearMap` / `MeasureTheory.Measure.addHaar_image_linearMap`
  (in `MeasureTheory.Measure.Lebesgue.EqHaar`) to compute the volume of the preimage of the
  cube as `|(LinearMap.det T)⁻¹| * (cube volume)`, where the cube
  `{y | ∀ k, |y k| < 1}` has volume `2^d` (use `Real.volume_pi_Ioo`).
* Convert ENNReal to real (`Measure.real`, `ENNReal.toReal_mul`, finite volume).
  `Dval d α v > 0` since `∏ v k > 0` and every `|α i − α j| > 0`.

The statement must remain EXACTLY as given (it is consumed by `Submission.MinkUpper`).
-/

namespace Submission.MinkVol

open Submission.MinkBox
/-- The weighted Vandermonde matrix `(wvMatrix α v) k j = v k * (α k)^j`. -/
def wvMatrix (d : ℕ) (α : Fin d → ℝ) (v : Fin d → ℝ) : Matrix (Fin d) (Fin d) ℝ :=
  fun k j => v k * (α k) ^ (j : ℕ)

/-- Multiplying `x` by `wvMatrix` equals the weighted polynomial evaluations. -/
lemma wvMatrix_mulVec_apply (d : ℕ) (α v : Fin d → ℝ) (x : Fin d → ℝ) (k : Fin d) :
    (Matrix.mulVec (wvMatrix d α v) x) k = v k * (∑ j : Fin d, x j * (α k) ^ j.val) := by
  rw [Matrix.mulVec_apply_eq_sum]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  simp only [wvMatrix]
  ring

/-- Determinant of the weighted Vandermonde matrix. -/
lemma wvMatrix_det (d : ℕ) (α v : Fin d → ℝ) :
    (wvMatrix d α v).det = (∏ k : Fin d, v k) * (Matrix.vandermonde α).det := by
  rw [← Matrix.det_mul_column v (Matrix.vandermonde α)]
  rfl

/-- `Ioi i` as a filter of the universe. -/
lemma Ioi_eq_filter (d : ℕ) (i : Fin d) :
    Finset.Ioi i = Finset.univ.filter (fun j : Fin d => i < j) := by
  ext j
  simp

/-- |det of the Vandermonde matrix| as product over `Ioi`. -/
lemma abs_det_vandermonde (d : ℕ) (α : Fin d → ℝ) :
    |(Matrix.vandermonde α).det| = ∏ i : Fin d, ∏ j ∈ Finset.Ioi i, |α i - α j| := by
  rw [Matrix.det_vandermonde]
  rw [Finset.abs_prod]
  refine Finset.prod_congr rfl ?_
  intro i _
  rw [Finset.abs_prod]
  refine Finset.prod_congr rfl ?_
  intro j _
  rw [abs_sub_comm]

/-- `pairProd` written with `Ioi`. -/
lemma pairProd_eq (d : ℕ) (α : Fin d → ℝ) :
    pairProd d α = ∏ i : Fin d, ∏ j ∈ Finset.Ioi i, |α i - α j| := by
  unfold pairProd
  refine Finset.prod_congr rfl ?_
  intro i _
  rw [Ioi_eq_filter d i]

/-- |det of the Vandermonde matrix| equals the MinkBox pair product. -/
lemma abs_det_vandermonde_eq_pairProd (d : ℕ) (α : Fin d → ℝ) :
    |(Matrix.vandermonde α).det| = pairProd d α := by
  rw [pairProd_eq]
  exact abs_det_vandermonde d α


/-- volume of the weighted Vandermonde body -/
theorem vol_weighted_vandermonde (d : ℕ) (α : Fin d → ℝ) (v : Fin d → ℝ)
    (hinj : Function.Injective α) (hv : ∀ k : Fin d, 0 < v k) :
    (MeasureTheory.volume : Measure (Fin d → ℝ)).real
      {x : Fin d → ℝ | ∀ k : Fin d, |v k * (∑ j : Fin d, x j * (α k) ^ j.val)| < 1} =
      (2 : ℝ) ^ d / Dval d α v := by
  classical
  let A : Matrix (Fin d) (Fin d) ℝ := wvMatrix d α v
  let T : (Fin d → ℝ) →ₗ[ℝ] (Fin d → ℝ) := Matrix.toLin' A
  let C : Set (Fin d → ℝ) := {y | ∀ k : Fin d, |y k| < 1}
  have hA_det : A.det = (∏ k : Fin d, v k) * (Matrix.vandermonde α).det := by
    exact wvMatrix_det d α v
  have hdet_ne : LinearMap.det T ≠ 0 := by
    rw [show LinearMap.det T = A.det by simp [T]]
    rw [hA_det]
    refine mul_ne_zero ?_ ?_
    · exact ne_of_gt (Finset.prod_pos (fun k hk => hv k))
    · exact Matrix.det_vandermonde_ne_zero_iff.mpr hinj
  have hdetT_eq : LinearMap.det T = (∏ k : Fin d, v k) * (Matrix.vandermonde α).det := by
    rw [show LinearMap.det T = A.det by simp [T]]
    exact hA_det
  have hAbsDet : |LinearMap.det T| = Dval d α v := by
    rw [hdetT_eq, abs_mul]
    rw [abs_of_pos (Finset.prod_pos (fun k hk => hv k))]
    rw [abs_det_vandermonde_eq_pairProd]
    rfl
  have hpre : T ⁻¹' C =
      {x : Fin d → ℝ | ∀ k : Fin d, |v k * (∑ j : Fin d, x j * (α k) ^ j.val)| < 1} := by
    ext x
    constructor <;> intro h k
    · have hk := h k
      simpa [C, T, A, wvMatrix_mulVec_apply] using hk
    · have hk := h k
      simpa [C, T, A, wvMatrix_mulVec_apply] using hk
  have hC_pi : C = Set.univ.pi (fun _ : Fin d => Set.Ioo (-1 : ℝ) 1) := by
    ext y
    simp [C, abs_lt]
  have hvolC : (volume C).toReal = (2 : ℝ) ^ d := by
    rw [hC_pi]
    rw [Real.volume_pi_Ioo_toReal (a := fun _ : Fin d => (-1 : ℝ))
      (b := fun _ : Fin d => (1 : ℝ))]
    · simp
      norm_num
    · intro i
      norm_num
  have hvol_pre : (volume (T ⁻¹' C)).toReal = |(LinearMap.det T)⁻¹| * (2 : ℝ) ^ d := by
    rw [addHaar_preimage_linearMap (μ := (volume : Measure (Fin d → ℝ))) (f := T) hdet_ne C]
    rw [ENNReal.toReal_mul]
    rw [hvolC]
    rw [ENNReal.toReal_ofReal (abs_nonneg _)]
  have hvol_pre' : (volume (T ⁻¹' C)).toReal = (Dval d α v)⁻¹ * (2 : ℝ) ^ d := by
    rw [hvol_pre]
    apply congrArg (fun c : ℝ => c * (2 : ℝ) ^ d)
    rw [abs_inv]
    rw [hAbsDet]
  have hvol_final : (volume (T ⁻¹' C)).toReal = (2 : ℝ) ^ d / Dval d α v := by
    rw [hvol_pre']
    rw [div_eq_mul_inv]
    ring
  rw [← hpre]
  rw [measureReal_def]
  exact hvol_final

end Submission.MinkVol
