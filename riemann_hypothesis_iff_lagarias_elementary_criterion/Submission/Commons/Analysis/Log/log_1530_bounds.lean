import Mathlib.Analysis.Complex.ExponentialBounds

namespace Commons.Analysis.Log

/-- Explicit rational bounds for the natural logarithm of 1530.
Provable e.g. from `log 1530 = log 3 + 9 * log 2 + log (1 - 1/256)`
together with the standard explicit bounds for log 2, log 3 and the series
`log (1 - t) ≤ -t`. -/
theorem log_1530_bounds :
    (7.3330 : ℝ) ≤ Real.log 1530 ∧ Real.log 1530 ≤ 7.33315 := by
  have hpos : (0 : ℝ) < 1 - 1 / 256 := by norm_num
  -- decomposition of 1530 = 3 * 2^9 * (1 - 1/256)
  have hdecomp : Real.log 1530 = Real.log 3 + 9 * Real.log 2 + Real.log (1 - 1 / 256) := by
    have h1530 : (1530 : ℝ) = 3 * 2 ^ 9 * (1 - 1 / 256) := by norm_num
    rw [h1530,
      Real.log_mul (by norm_num) (by norm_num),
      Real.log_mul (by norm_num) (by norm_num),
      Real.log_pow]
    ring
  -- bounds for log (1 - 1/256)
  have hS_up : Real.log (1 - 1 / 256) ≤ -(1 / 256 : ℝ) := by
    have := Real.log_le_sub_one_of_pos hpos
    linarith
  have hS_low : -(1 / 255 : ℝ) ≤ Real.log (1 - 1 / 256) := by
    have := Real.one_sub_inv_le_log_of_pos hpos
    have hx : (1 - 1 / 256 : ℝ)⁻¹ = 256 / 255 := by norm_num
    rw [hx] at this
    linarith
  -- explicit bounds for log 2 and log 3
  have h2l := Real.log_two_gt_d9
  have h2u := Real.log_two_lt_d9
  have h3l := Real.log_three_gt_d9
  have h3u := Real.log_three_lt_d9
  rw [hdecomp]
  constructor <;> linarith

end Commons.Analysis.Log