import Mathlib.Analysis.InnerProductSpace.Calculus

namespace Commons.Analysis.Calculus.FDeriv

open scoped RealInnerProductSpace in
theorem fderiv_rho_eq {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (x w : E) :
    fderiv ℝ (fun z : E => 9 - ‖z‖ ^ 2) x w = -2 * ⟪x, w⟫ := by
  have h1 : HasFDerivAt (fun _ : E => (9 : ℝ)) (0 : E →L[ℝ] ℝ) x :=
    hasFDerivAt_const (9 : ℝ) x
  have h2 : HasFDerivAt (fun z : E => ‖z‖ ^ 2) (2 • innerSL ℝ x) x :=
    (hasStrictFDerivAt_norm_sq x).hasFDerivAt
  have h3 : fderiv ℝ (fun z : E => 9 - ‖z‖ ^ 2) x = (0 : E →L[ℝ] ℝ) - (2 • innerSL ℝ x) :=
    (h1.sub h2).fderiv
  rw [h3]
  simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.zero_apply,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.neg_apply,
    innerSL_apply_apply, zero_sub, smul_eq_mul]
  ring

end Commons.Analysis.Calculus.FDeriv