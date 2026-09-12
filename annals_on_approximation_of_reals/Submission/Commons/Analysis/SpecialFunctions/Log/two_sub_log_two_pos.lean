import Mathlib.Analysis.SpecialFunctions.Log.Basic

open Real

namespace Commons.Analysis.SpecialFunctions.Log

lemma two_sub_log_two_pos : 0 < 2 - log 2 := by
  have hlog_lt_one : log 2 < 1 := by
    have h := log_lt_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)
      (show (2 : ℝ) ≠ 1 by norm_num)
    norm_num at h
    exact h
  linarith

end Commons.Analysis.SpecialFunctions.Log
