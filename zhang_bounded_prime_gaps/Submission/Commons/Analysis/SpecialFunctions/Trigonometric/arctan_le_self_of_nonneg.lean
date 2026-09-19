import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Submission.Commons.Analysis.SpecialFunctions.Gamma.gammaR_log_norm_sub_le

namespace Commons.Analysis.SpecialFunctions.Trigonometric

/-- For nonnegative real `x`, `arctan x ≤ x`. -/
theorem arctan_le_self_of_nonneg {x : ℝ} (hx : 0 ≤ x) : Real.arctan x ≤ x := by
  have hderiv : ∀ t : ℝ, deriv Real.arctan t ≤ 1 := by
    intro t
    rw [Real.deriv_arctan]
    change 1 / (1 + t ^ 2) ≤ 1
    have hden : 0 < 1 + t ^ 2 := by positivity
    rw [div_le_iff₀ hden]
    nlinarith [sq_nonneg t]
  have h := image_sub_le_mul_sub_of_deriv_le (f := Real.arctan) (C := 1)
    Real.differentiable_arctan hderiv hx
  simpa using h

end Commons.Analysis.SpecialFunctions.Trigonometric