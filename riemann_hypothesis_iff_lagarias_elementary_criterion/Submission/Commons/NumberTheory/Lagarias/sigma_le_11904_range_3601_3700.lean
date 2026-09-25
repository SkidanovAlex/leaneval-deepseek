import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.Tactic.IntervalCases

set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

namespace Commons.NumberTheory.Lagarias

theorem sigma_le_11904_range_3601_3700 (n : ℕ) (hL : 3601 ≤ n) (hU : n ≤ 3700) :
    (ArithmeticFunction.sigma 1 n : ℕ) ≤ 11904 := by
  interval_cases n <;> decide

end Commons.NumberTheory.Lagarias