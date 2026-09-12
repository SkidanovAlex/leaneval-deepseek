import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace Commons.Analysis.SpecialFunctions.Log

open Real

lemma three_sub_two_mul_add_log_le (t : ℝ) (ht : 0 < t) :
    3 - 2 * t + log t ≤ 2 - log 2 := by
  have ht2 : 0 < 2 * t := by positivity
  have hle : log (2 * t) ≤ 2 * t - 1 := log_le_sub_one_of_pos ht2
  have hlog : log (2 * t) = log 2 + log t := by
    rw [log_mul (by norm_num : (2 : ℝ) ≠ 0) (ne_of_gt ht)]
  linarith

end Commons.Analysis.SpecialFunctions.Log