import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace Commons.Analysis.Real

theorem log_one_add_ge_two_mul_div {z : ℝ} (hz : 0 ≤ z) :
    2 * z / (2 + z) ≤ Real.log (1 + z) := by
  rw [add_comm (2:ℝ) z]
  exact Real.le_log_one_add_of_nonneg hz

end Commons.Analysis.Real