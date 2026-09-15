import Mathlib.Analysis.SpecialFunctions.Log.Deriv

namespace Commons.Analysis.ExpLog

open scoped Real
open Finset

/-- Lower bound for `log ((1+r)/(1−r))` by the partial sum of its (all-positive)
power series `2·Σ r^(2k+1)/(2k+1)` for `0 < r < 1`: the truncated sum is a
lower bound. -/
theorem atanh_series_log_lower {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) (N : ℕ) :
    2 * (Finset.sum (Finset.range (N + 1)) (fun k => r ^ (2 * k + 1) / (2 * k + 1 : ℝ))) ≤
      Real.log ((1 + r) / (1 - r)) := by
  have h := Real.sum_range_le_log_div (le_of_lt hr0) hr1 (N + 1)
  calc
    2 * (Finset.sum (Finset.range (N + 1)) (fun k => r ^ (2 * k + 1) / (2 * k + 1 : ℝ)))
        ≤ 2 * (1 / 2 * Real.log ((1 + r) / (1 - r))) := by
          exact mul_le_mul_of_nonneg_left h (by norm_num)
    _ = Real.log ((1 + r) / (1 - r)) := by ring

end Commons.Analysis.ExpLog
