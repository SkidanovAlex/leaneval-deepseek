import Mathlib

namespace Work.TMC16Core.Core

/-- Arithmetic bookkeeping for the Avila–Jitomirskaya Ten Martini Problem.

The β-terms on the two sides agree exactly:
`(2q-1) * (β/2 + β/(4q-2)) = β*q`, so the inequality is really a pure inequality
between logarithms.  Concretely the right-hand side is at least
`β*q + (2*log (1/c) + 200*log q + 200)`, which dominates
`β*q + 64*log q + 2*log (1/(2c)) + 1` because `log q ≥ 0`, `log (1/c) ≥ 0`,
`log 2 ≥ 0`. -/
theorem res_arith {β q c : ℝ} (hq1 : 1 ≤ q) (hc0 : 0 < c) (hc1 : c ≤ 1) :
    β * q + 64 * Real.log q + 2 * Real.log (1 / (2 * c)) + 1 ≤
      (2 * q - 1) * (β / 2 + β / (4 * q - 2) + 2 * Real.log (1 / c) / q
        + 200 * Real.log q / q + 200 / q) := by
  have hq0 : (0 : ℝ) < q := by linarith
  have h4 : (4 * q - 2) ≠ 0 := by intro h; nlinarith [hq1]
  have hL : 0 ≤ Real.log q := Real.log_nonneg hq1
  have hM : 0 ≤ Real.log (1 / c) :=
    Real.log_nonneg (by rw [one_le_div hc0]; exact hc1)
  have ht0 : 0 ≤ Real.log 2 := le_of_lt (Real.log_pos (by norm_num : (1 : ℝ) < 2))
  have hlog : Real.log (1 / (2 * c)) = Real.log (1 / c) - Real.log 2 := by
    rw [show (1 : ℝ) / (2 * c) = (1 / c) / 2 by ring]
    rw [Real.log_div (by positivity) (by norm_num)]
  -- the β-terms agree exactly
  have hbeta : (2 * q - 1) * (β / 2 + β / (4 * q - 2)) = β * q := by
    have h2 : (2 : ℝ) ≠ 0 := by norm_num
    have hqid : (2 * q - 1) / 2 + (2 * q - 1) / (4 * q - 2) = q := by
      rw [div_add_div _ _ h2 h4]
      rw [div_eq_iff (show (2 : ℝ) * (4 * q - 2) ≠ 0 by intro h; nlinarith [hq1])]
      ring
    calc (2 * q - 1) * (β / 2 + β / (4 * q - 2))
        = β * ((2 * q - 1) / 2 + (2 * q - 1) / (4 * q - 2)) := by ring
      _ = β * q := by rw [hqid]
  -- numeric part
  have hA : 64 * Real.log q + 2 * (Real.log (1 / c) - Real.log 2) + 1 ≤
      2 * Real.log (1 / c) + 200 * Real.log q + 200 := by
    linarith [hL, ht0]
  have hY : 0 ≤ 2 * Real.log (1 / c) + 200 * Real.log q + 200 := by
    linarith [hL, hM]
  have hB : 2 * Real.log (1 / c) + 200 * Real.log q + 200 ≤
      (2 * q - 1) * (2 * Real.log (1 / c) / q + 200 * Real.log q / q + 200 / q) := by
    have heq : (2 * q - 1) * (2 * Real.log (1 / c) / q + 200 * Real.log q / q + 200 / q)
        = (2 * q - 1) * (2 * Real.log (1 / c) + 200 * Real.log q + 200) / q := by
      rw [show 2 * Real.log (1 / c) / q + 200 * Real.log q / q + 200 / q
            = (2 * Real.log (1 / c) + 200 * Real.log q + 200) / q by ring]
      ring
    rw [heq, le_div_iff₀ hq0]
    have hprod : 0 ≤ (2 * Real.log (1 / c) + 200 * Real.log q + 200) * (q - 1) :=
      mul_nonneg hY (by linarith)
    nlinarith [hprod]
  have hfinal : (2 * q - 1) * (β / 2 + β / (4 * q - 2) + 2 * Real.log (1 / c) / q
        + 200 * Real.log q / q + 200 / q)
      = β * q + (2 * q - 1) * (2 * Real.log (1 / c) / q + 200 * Real.log q / q + 200 / q) := by
    rw [show (β / 2 + β / (4 * q - 2) + 2 * Real.log (1 / c) / q
          + 200 * Real.log q / q + 200 / q)
        = (β / 2 + β / (4 * q - 2)) + (2 * Real.log (1 / c) / q + 200 * Real.log q / q + 200 / q) by ring]
    rw [mul_add, hbeta]
  rw [hlog, hfinal]
  linarith [hA, hB]

end Work.TMC16Core.Core
