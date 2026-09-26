import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.InnerProductSpace.Basic

namespace Commons.Analysis.Calculus.Deriv

/-- A `C¹` function from `ℝ` to a normed real space has a continuous (Fréchet)
derivative `deriv f`.  This is exactly the scalar half of Mathlib's
`ContDiff.continuous_deriv_one` (the derivative in the direction `1 : ℝ`). -/
theorem continuous_deriv_of_contDiff_one {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : ℝ → F} (h : ContDiff ℝ 1 f) : Continuous (deriv f) := by
  exact h.continuous_deriv_one

end Commons.Analysis.Calculus.Deriv