import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.Tactic.IntervalCases

set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

namespace Commons.NumberTheory.Lagarias

theorem sigma_le_12264_range_3801_3900 (n : ℕ) (hL : 3801 ≤ n) (hU : n ≤ 3900) :
    (ArithmeticFunction.sigma 1 n : ℕ) ≤ 12264 := by
  interval_cases n <;> decide

end Commons.NumberTheory.Lagarias