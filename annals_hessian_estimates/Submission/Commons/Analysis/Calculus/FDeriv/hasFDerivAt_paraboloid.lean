import Mathlib.Analysis.InnerProductSpace.Calculus

namespace Commons.Analysis.Calculus.FDeriv

open scoped RealInnerProductSpace in
/-- The paraboloid `z ↦ a / 2 * ‖z - y‖ ^ 2` has derivative `a • innerSL ℝ (x - y)` at `x`:
the gradient of `(a/2)‖z - y‖²` at `x` is `a (x - y)`, viewed as the continuous linear
functional `w ↦ ⟪a (x - y), w⟫ = a ⟪x - y, w⟫`. -/
theorem hasFDerivAt_paraboloid {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] (a : ℝ) (y x : E) :
    HasFDerivAt (fun z : E => a / 2 * ‖z - y‖ ^ 2) (a • innerSL ℝ (x - y)) x := by
  -- derivative of `z ↦ z - y` is the identity
  have h1 : HasFDerivAt (fun z : E => z - y) (ContinuousLinearMap.id ℝ E) x := by
    simpa using (hasFDerivAt_id x).sub_const y
  -- derivative of `z ↦ ‖z - y‖ ^ 2` is `2 • innerSL ℝ (x - y)`
  have h2 : HasFDerivAt (fun z : E => ‖z - y‖ ^ 2) (2 • innerSL ℝ (x - y)) x := by
    simpa [ContinuousLinearMap.comp_id] using h1.norm_sq
  -- multiply by the constant `a / 2`
  have h3 := h2.const_mul (a / 2)
  -- `(a / 2) • (2 • innerSL ℝ (x - y)) = a • innerSL ℝ (x - y)`
  have hd : ((a / 2) • (2 • innerSL ℝ (x - y)) : E →L[ℝ] ℝ) = a • innerSL ℝ (x - y) := by
    ext w
    simp only [smul_apply, smul_eq_mul]
    ring
  exact h3.congr_fderiv hd

end Commons.Analysis.Calculus.FDeriv