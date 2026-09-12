import Mathlib.Analysis.SpecialFunctions.Log.Basic

open Real

namespace Commons.Analysis.SpecialFunctions.Log

lemma mul_log_one_add_inv_le_one (t : ℝ) (ht : 0 < t) :
    t * log (1 + 1 / t) ≤ 1 := by
  have hx : 0 < 1 + 1 / t := by positivity
  have hlog : log (1 + 1 / t) ≤ (1 + 1 / t) - 1 :=
    log_le_sub_one_of_pos hx
  calc
    t * log (1 + 1 / t) ≤ t * ((1 + 1 / t) - 1) :=
      mul_le_mul_of_nonneg_left hlog (le_of_lt ht)
    _ = 1 := by
      field_simp [ne_of_gt ht]
      ring

end Commons.Analysis.SpecialFunctions.Log
