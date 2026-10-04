import Submission.Work.Diff.C.LDG.Defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The Euclidean normalization map `z ↦ ‖z‖⁻¹ • z` and its derivative
-/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology EuclideanSpace
open Bundle ContDiff Set VectorField CovariantDerivative Metric

namespace Work.Diff.C.LDG

variable {ι : Type*} [Fintype ι]

/-- `(‖z‖²)^(-1/2) = ‖z‖⁻¹`, everywhere (both sides vanish at `z = 0`). -/
theorem rpow_neg_half_norm_sq (z : EuclideanSpace ℝ ι) :
    (‖z‖ ^ 2) ^ (-(1/2) : ℝ) = ‖z‖⁻¹ := by
  rcases eq_or_ne z 0 with rfl | hz
  · simp [Real.zero_rpow]
  · rw [← Real.rpow_natCast (‖z‖) 2, ← Real.rpow_mul (norm_nonneg z)]
    rw [show ((2 : ℕ) : ℝ) * (-(1/2)) = (-1 : ℝ) by norm_num]
    exact Real.rpow_neg_one ‖z‖

/-- `(‖z‖²)^(-3/2) = (‖z‖³)⁻¹`. -/
theorem rpow_neg_three_half_norm_sq (z : EuclideanSpace ℝ ι) :
    (‖z‖ ^ 2) ^ (-(3/2) : ℝ) = (‖z‖ ^ 3)⁻¹ := by
  rcases eq_or_ne z 0 with rfl | hz
  · simp [Real.zero_rpow]
  · rw [← Real.rpow_natCast (‖z‖) 2, ← Real.rpow_mul (norm_nonneg z)]
    rw [show ((2 : ℕ) : ℝ) * (-(3/2)) = (-3 : ℝ) by norm_num]
    rw [Real.rpow_neg (norm_nonneg z) 3]
    exact congrArg Inv.inv (Real.rpow_natCast (‖z‖) 3)

/-- The derivative of the normalization map. -/
theorem fderiv_normalize (y : EuclideanSpace ℝ ι) (hy : y ≠ 0) :
    fderiv ℝ (fun z : EuclideanSpace ℝ ι => ‖z‖⁻¹ • z) y
      = ‖y‖⁻¹ • (1 : EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι)
        - (‖y‖ ^ 3)⁻¹ • (innerSL ℝ y).smulRight y := by
  have hfun : (fun z : EuclideanSpace ℝ ι => ‖z‖⁻¹ • z)
      = fun z : EuclideanSpace ℝ ι => (‖z‖ ^ 2) ^ (-(1/2) : ℝ) • z := by
    funext z
    rw [rpow_neg_half_norm_sq]
  have hbase := (hasStrictFDerivAt_norm_sq y).hasFDerivAt
  have hne : ‖y‖ ^ 2 ≠ 0 := by positivity
  have hc := hbase.rpow_const (p := -(1/2)) (Or.inl hne)
  have hid : HasFDerivAt (fun z : EuclideanSpace ℝ ι => z)
      (1 : EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι) y := hasFDerivAt_id y
  have hsmul := hc.smul hid
  have hfuneq : (fun z : EuclideanSpace ℝ ι => (‖z‖ ^ 2) ^ (-(1/2) : ℝ) • z)
      = ((fun z : EuclideanSpace ℝ ι => (‖z‖ ^ 2) ^ (-(1/2) : ℝ)) • fun z : EuclideanSpace ℝ ι => z) :=
    rfl
  rw [hfun, hfuneq, hsmul.fderiv]
  ext w
  simp only [add_apply, sub_apply, smul_apply, ContinuousLinearMap.smulRight_apply,
    smul_eq_mul, innerSL_apply_apply, nsmul_eq_mul, one_apply_eq_self, id_eq]
  rw [show (-(1/2) - 1 : ℝ) = -(3/2) by norm_num, rpow_neg_half_norm_sq y,
    rpow_neg_three_half_norm_sq y]
  rw [show (-(1/2) : ℝ) * (‖y‖ ^ 3)⁻¹ * (((2 : ℕ) : ℝ) * Inner.inner ℝ y w)
      = -((‖y‖ ^ 3)⁻¹ * Inner.inner ℝ y w) by ring, neg_smul]
  simp only [sub_eq_add_neg, one_apply_eq_self, smul_eq_mul, smul_smul]

/-- The value of the derivative of the normalization map. -/
theorem fderiv_normalize_apply (y : EuclideanSpace ℝ ι) (hy : y ≠ 0)
    (w : EuclideanSpace ℝ ι) :
    fderiv ℝ (fun z : EuclideanSpace ℝ ι => ‖z‖⁻¹ • z) y w
      = ‖y‖⁻¹ • w - ((‖y‖ ^ 3)⁻¹ * Inner.inner ℝ y w) • y := by
  rw [fderiv_normalize y hy]
  simp only [sub_apply, smul_apply, ContinuousLinearMap.smulRight_apply, smul_eq_mul,
    innerSL_apply_apply, smul_smul, one_apply_eq_self]

end Work.Diff.C.LDG
