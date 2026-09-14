import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

set_option linter.unusedVariables false

namespace Commons.Analysis.Integral

/-- `∫₀^b t ^ (-2/3) dt = 3 b ^ (1/3)`, scaled by the constant `c`.

This is the elementary power-rule antiderivative `∫ t ^ r = t ^ (r+1) / (r+1)`
applied with `r = -2/3 > -1`, so the improper integral converges at `t = 0`. -/
theorem rpow_neg_two_thirds_integral {b c : ℝ} (hb : 0 ≤ b) :
    ∫ t in (0:ℝ)..b, c * t ^ (-(2:ℝ)/3) = c * (3 * b ^ ((1:ℝ)/3)) := by
  -- pull the constant factor out of the interval integral
  rw [intervalIntegral.integral_const_mul]
  -- power rule: ∫ t in a..b, t ^ r = (b ^ (r+1) - a ^ (r+1)) / (r+1) for r > -1
  rw [integral_rpow (Or.inl (by norm_num : (-1:ℝ) < -(2:ℝ)/3))]
  have h1 : -(2:ℝ)/3 + 1 = (1:ℝ)/3 := by norm_num
  rw [h1, Real.zero_rpow (by norm_num : ((1:ℝ)/3) ≠ 0), sub_zero]
  congr 1
  rw [div_eq_mul_inv]
  norm_num
  ring

end Commons.Analysis.Integral