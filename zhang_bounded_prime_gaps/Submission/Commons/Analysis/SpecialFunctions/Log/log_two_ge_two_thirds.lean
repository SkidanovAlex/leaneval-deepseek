import Mathlib.Analysis.Complex.ExponentialBounds

namespace Commons.Analysis.SpecialFunctions.Log

theorem log_two_ge_two_thirds : (2 / 3 : ℝ) ≤ Real.log 2 := by
  have h : (2 / 3 : ℝ) < (0.6931471803 : ℝ) := by norm_num
  exact le_of_lt (h.trans Real.log_two_gt_d9)

end Commons.Analysis.SpecialFunctions.Log