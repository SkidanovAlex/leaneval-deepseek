import Mathlib
import Submission.Commons.Analysis.InnerProductSpace.fderiv_norm_eq

namespace Commons.Analysis.InnerProductSpace

open scoped RealInnerProductSpace InnerProductSpace

/-- **Chain rule for radial functions, first order.**
If `φ : ℝ → ℝ` is differentiable at `‖y‖` and `y ≠ 0`, then the derivative of
`z ↦ φ ‖z‖` at `y` in direction `v` is `deriv φ ‖y‖ * (⟪y, v⟫ / ‖y‖)`. -/
theorem fderiv_comp_norm_eq {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {φ : ℝ → ℝ} {y : E} (hy : y ≠ 0) (hφ : DifferentiableAt ℝ φ ‖y‖) (v : E) :
    (fderiv ℝ (fun z : E => φ ‖z‖) y) v = deriv φ ‖y‖ * (inner ℝ y v / ‖y‖) := by
  have hy2 : ‖y‖ ^ 2 ≠ 0 := pow_ne_zero _ (norm_ne_zero_iff.mpr hy)
  have hfun : (fun z : E => Real.sqrt (‖z‖ ^ 2)) = fun z : E => ‖z‖ :=
    funext fun z => Real.sqrt_sq (norm_nonneg z)
  -- differentiability of the norm at `y`, obtained via `√(‖·‖²)`
  have hsq : HasFDerivAt (fun z : E => ‖z‖ ^ 2) (2 • innerSL ℝ y) y :=
    (hasStrictFDerivAt_norm_sq y).hasFDerivAt
  have hsqrt : HasFDerivAt Real.sqrt
      (ContinuousLinearMap.toSpanSingleton ℝ (1 / (2 * Real.sqrt (‖y‖ ^ 2)))) (‖y‖ ^ 2) :=
    (Real.hasDerivAt_sqrt hy2).hasFDerivAt
  have hnormDiff : DifferentiableAt ℝ (fun z : E => ‖z‖) y := by
    have hc : HasFDerivAt (fun z : E => Real.sqrt (‖z‖ ^ 2))
        ((ContinuousLinearMap.toSpanSingleton ℝ (1 / (2 * Real.sqrt (‖y‖ ^ 2)))).comp
          (2 • innerSL ℝ y)) y := hsqrt.comp y hsq
    have : DifferentiableAt ℝ (fun z : E => Real.sqrt (‖z‖ ^ 2)) y := hc.differentiableAt
    rwa [hfun] at this
  -- chain rule, then evaluate
  rw [show (fun z : E => φ ‖z‖) = φ ∘ fun z : E => ‖z‖ from rfl,
    fderiv_comp y hφ hnormDiff, ContinuousLinearMap.comp_apply, fderiv_eq_deriv_mul,
    fderiv_norm_eq hy v]

end Commons.Analysis.InnerProductSpace
