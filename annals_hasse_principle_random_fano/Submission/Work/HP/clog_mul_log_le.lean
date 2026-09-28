import Mathlib
import Submission.Work.HP.Defs

namespace Work.HP

/-- For a prime `p` and `2 ≤ n`, the ceiling logarithm of `n` to base `p`, times `log p`,
is at most `log n + log p`. This is the estimate `clog_p n · log p ≤ log n + log p`,
coming from `p ^ (clog_p n - 1) < n`. -/
theorem clog_mul_log_le (p n : ℕ) (hp : p.Prime) (hn : 2 ≤ n) :
    (Nat.clog p n : ℝ) * Real.log (p : ℝ) ≤ Real.log (n : ℝ) + Real.log (p : ℝ) := by
  have hp2 : 1 < p := hp.one_lt
  have hn1 : 1 < n := by omega
  have hpos : 0 < Nat.clog p n := Nat.clog_pos hp2 hn1
  -- `p ^ (clog_p n - 1) < n`, so taking `log` gives `(clog_p n - 1) log p < log n`.
  have hlt : p ^ (Nat.clog p n).pred < n := Nat.pow_pred_clog_lt_self hp2 hn1
  have hloglt : Real.log ((p : ℝ) ^ (Nat.clog p n).pred) < Real.log (n : ℝ) :=
    Real.log_lt_log (by positivity) (by exact_mod_cast hlt)
  rw [Real.log_pow] at hloglt
  have hcast : ((Nat.clog p n).pred : ℝ) = (Nat.clog p n : ℝ) - 1 := Nat.cast_pred hpos
  rw [hcast] at hloglt
  -- `(clog_p n) log p - log p < log n`, hence `(clog_p n) log p < log n + log p`.
  have : (Nat.clog p n : ℝ) * Real.log (p : ℝ) < Real.log (n : ℝ) + Real.log (p : ℝ) := by
    linarith
  linarith

end Work.HP
