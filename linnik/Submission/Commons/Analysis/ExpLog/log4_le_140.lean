import Mathlib.Analysis.Complex.ExponentialBounds

namespace Commons.Analysis.ExpLog

theorem log4_le_140 : Real.log 4 ≤ (7 : ℝ) / 5 := by
  rw [Real.log_four_eq]
  have h : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
  have hmul : 2 * Real.log 2 < 2 * (0.6931471808 : ℝ) := by
    exact mul_lt_mul_of_pos_left h (by norm_num)
  nlinarith

end Commons.Analysis.ExpLog