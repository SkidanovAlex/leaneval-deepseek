import Mathlib.Analysis.Complex.ExponentialBounds

namespace Commons.Analysis.LogBounds

theorem log_two_ge_half : (1 / 2 : ℝ) ≤ Real.log 2 := by
  linarith [Real.log_two_gt_d9]

end Commons.Analysis.LogBounds