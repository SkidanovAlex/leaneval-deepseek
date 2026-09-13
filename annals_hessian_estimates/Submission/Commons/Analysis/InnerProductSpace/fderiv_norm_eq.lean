import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.InnerProductSpace.Calculus

/-!
# The Fréchet derivative of the norm on a real inner product space

For `y ≠ 0` in a real inner product space `E`, the norm `z ↦ ‖z‖` is differentiable at `y` with
Fréchet derivative `v ↦ ⟪y, v⟫ / ‖y‖`.  We obtain this as a chain rule application: near a
nonzero point the norm is the square root of the squared norm, and the derivative of the squared
norm is the continuous linear map `2 • innerSL ℝ y`.
-/

open scoped RealInnerProductSpace

namespace Commons.Analysis.InnerProductSpace

/-- The Fréchet derivative of the norm at a nonzero point `y`, evaluated at `v`, is the
normalized inner product `⟪y, v⟫ / ‖y‖`. -/
theorem fderiv_norm_eq {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {y : E} (hy : y ≠ 0) (v : E) :
    (fderiv ℝ (fun z : E => ‖z‖) y) v = inner ℝ y v / ‖y‖ := by
  have hy2 : ‖y‖ ^ 2 ≠ 0 := pow_ne_zero _ (norm_ne_zero_iff.mpr hy)
  -- derivative of the squared norm
  have hsq : HasFDerivAt (fun z : E => ‖z‖ ^ 2) (2 • innerSL ℝ y) y :=
    (hasStrictFDerivAt_norm_sq y).hasFDerivAt
  -- derivative of `Real.sqrt` at `‖y‖ ^ 2`
  have hsqrt : HasFDerivAt Real.sqrt
      (ContinuousLinearMap.toSpanSingleton ℝ (1 / (2 * Real.sqrt (‖y‖ ^ 2)))) (‖y‖ ^ 2) :=
    (Real.hasDerivAt_sqrt hy2).hasFDerivAt
  -- chain rule: the norm is `√(‖·‖²)` near `y`
  have hcomp : HasFDerivAt (fun z : E => Real.sqrt (‖z‖ ^ 2))
      ((ContinuousLinearMap.toSpanSingleton ℝ (1 / (2 * Real.sqrt (‖y‖ ^ 2)))).comp
        (2 • innerSL ℝ y)) y := hsqrt.comp y hsq
  have hfun : (fun z : E => Real.sqrt (‖z‖ ^ 2)) = fun z : E => ‖z‖ :=
    funext fun z => Real.sqrt_sq (norm_nonneg z)
  rw [hfun] at hcomp
  rw [hcomp.fderiv]
  simp only [ContinuousLinearMap.comp_apply, smul_apply,
    ContinuousLinearMap.toSpanSingleton_apply, innerSL_apply_apply,
    Real.sqrt_sq (norm_nonneg y), smul_eq_mul]
  rw [div_eq_mul_inv]
  field_simp
  ring

end Commons.Analysis.InnerProductSpace