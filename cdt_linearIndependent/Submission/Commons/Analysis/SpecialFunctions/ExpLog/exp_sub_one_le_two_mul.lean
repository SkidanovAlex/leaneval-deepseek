import Mathlib.Analysis.Complex.Exponential

namespace Commons.Analysis.SpecialFunctions.ExpLog

/-- For `0 ≤ t ≤ 1/2`, `exp t - 1 ≤ 2 t`. Follows from Mathlib's `Real.abs_exp_sub_one_le`,
since `exp t ≥ 1` and `|t| = t`. -/
theorem exp_sub_one_le_two_mul (t : ℝ) (h0 : 0 ≤ t) (h1 : t ≤ 1 / 2) :
    Real.exp t - 1 ≤ 2 * t := by
  have hx : |t| ≤ 1 := by rw [abs_of_nonneg h0]; linarith
  have h := Real.abs_exp_sub_one_le hx
  have hge : 0 ≤ Real.exp t - 1 := by linarith [Real.one_le_exp h0]
  rw [abs_of_nonneg hge, abs_of_nonneg h0] at h
  exact h

end Commons.Analysis.SpecialFunctions.ExpLog