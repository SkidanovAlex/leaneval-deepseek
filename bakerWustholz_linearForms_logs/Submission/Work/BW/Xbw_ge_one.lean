import Mathlib
import Submission.Work.BW.Defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

/-! ### `X(n,d) ≥ 1`

`X(n,d) = log C(n,d) − n log d − log(n+d)` where
`C(n,d) = 18 (n+1)! n^{n+1} (32d)^{n+2} log(2nd)`.

Expanding `log C(n,d)` (all factors positive for `n,d ≥ 1` and splitting
`(n+2) log(32d) = (n+2) log 32 + (n+2) log d`) the term `n log d` cancels and

`X(n,d) = log 18 + log((n+1)!) + (n+1) log n + (n+2) log 32 + 2 log d
          + log log(2nd) − log(n+d)`.

Every term except the last is nonnegative, `(n+1) log n ≥ log n + log 2` for `n ≥ 2`, and
`log(n+d) ≤ log(2nd) = log 2 + log n + log d`; hence `X(n,d) ≥ log 18 ≥ 1`
(the true minimum is `≈ 19.85` at `(n,d) = (2,1)`, so the bound is very slack). -/

/-- Expansion of `X(n,d)` into a sum of logarithms. -/
private lemma Xbw_eq (n d : ℕ) (hn : 1 ≤ n) (hd : 1 ≤ d) :
    Xbw n d = Real.log 18 + Real.log ((n + 1).factorial : ℝ) + ((n : ℝ) + 1) * Real.log (n : ℝ)
      + ((n : ℝ) + 2) * Real.log 32 + 2 * Real.log (d : ℝ)
      + Real.log (Real.log (2 * (n : ℝ) * (d : ℝ))) - Real.log ((n : ℝ) + (d : ℝ)) := by
  have hn1 : (1:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn
  have hd1 : (1:ℝ) ≤ (d:ℝ) := by exact_mod_cast hd
  have hn0 : (0:ℝ) < (n:ℝ) := lt_of_lt_of_le one_pos hn1
  have hd0 : (0:ℝ) < (d:ℝ) := lt_of_lt_of_le one_pos hd1
  have hL0 : (0:ℝ) < Real.log (2 * (n:ℝ) * (d:ℝ)) := by
    apply Real.log_pos; nlinarith
  rw [Xbw, BakerWustholz.C,
      Real.log_mul (by positivity) (by positivity),
      Real.log_mul (by positivity) (by positivity),
      Real.log_mul (by positivity) (by positivity),
      Real.log_mul (by positivity) (by positivity),
      Real.log_pow, Real.log_pow,
      Real.log_mul (by norm_num : (32:ℝ) ≠ 0) (by positivity : (d:ℝ) ≠ 0)]
  push_cast
  ring

/-- `X(n,d) = log C(n,d) − n log d − log(n+d) ≥ 1` for `n ≥ 2`, `d ≥ 1`, where
`C(n,d) = 18 (n+1)! n^{n+1} (32d)^{n+2} log(2nd)`.

*Proof:* `log C(n,d) = log 18 + log((n+1)!) + (n+1) log n + (n+2) log(32d) + log log(2nd)` and
`(n+2) log(32d) − n log d = 2 log(32d) + n log 32`, so it suffices to bound
`log(n+d) ≤ (n+1) log n + 2 log(32d) + n log 32 + log 18 + log log(2nd) − 1`; use
`log(n+d) ≤ log(2 max(n,d))` and `max ≤ n + d ≤ nd + 2`, or split off `d ≥ 3` versus `d ∈ {1,2}`.
The bound has enormous slack (the minimum is `≈ 19.85` at `(n,d) = (2,1)`). -/
theorem Xbw_ge_one (n d : ℕ) (hn : 2 ≤ n) (hd : 1 ≤ d) : 1 ≤ Xbw n d := by
  have hn1 : 1 ≤ n := by omega
  have hn2 : (2:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn
  have hd1 : (1:ℝ) ≤ (d:ℝ) := by exact_mod_cast hd
  have hn0 : (0:ℝ) < (n:ℝ) := by linarith
  have hd0 : (0:ℝ) < (d:ℝ) := by linarith
  have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogn : Real.log 2 ≤ Real.log (n:ℝ) := Real.log_le_log (by norm_num) hn2
  have hf : 0 ≤ Real.log ((n+1).factorial : ℝ) := by
    apply Real.log_nonneg
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero (n+1))
  have h32 : 0 ≤ Real.log 32 := Real.log_nonneg (by norm_num)
  have hlogd : 0 ≤ Real.log (d:ℝ) := Real.log_nonneg hd1
  have hL : 0 ≤ Real.log (Real.log (2*(n:ℝ)*(d:ℝ))) := by
    apply Real.log_nonneg
    rw [Real.le_log_iff_exp_le (by positivity)]
    have := Real.exp_one_lt_three
    nlinarith
  have hnd : Real.log ((n:ℝ)+(d:ℝ)) ≤ Real.log 2 + Real.log (n:ℝ) + Real.log (d:ℝ) := by
    have h1 : (0:ℝ) < (n:ℝ) + (d:ℝ) := by linarith
    have h2 : (n:ℝ) + (d:ℝ) ≤ 2 * (n:ℝ) * (d:ℝ) := by nlinarith
    calc Real.log ((n:ℝ)+(d:ℝ)) ≤ Real.log (2 * (n:ℝ) * (d:ℝ)) := Real.log_le_log h1 h2
      _ = Real.log 2 + Real.log (n:ℝ) + Real.log (d:ℝ) := by
          rw [Real.log_mul (by positivity) (by positivity),
              Real.log_mul (by positivity) (by positivity)]
  have h18 : (1:ℝ) ≤ Real.log 18 := by
    rw [Real.le_log_iff_exp_le (by norm_num)]
    have := Real.exp_one_lt_three; linarith
  rw [Xbw_eq n d hn1 hd]
  nlinarith [h18, hf, hlogn, hlog2pos, hn2, h32, hlogd, hL, hnd]

end Work.BW
