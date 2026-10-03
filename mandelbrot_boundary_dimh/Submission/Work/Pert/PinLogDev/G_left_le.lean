import Mathlib
import Submission.Work.Pert.PinLogDev.Prim

namespace Work.Pert.PinLogDev

/-- On the negative half-line, `G` is the difference of two logarithms, so the increment of `G`
over `[p, p+L]` (with `p + L ≤ 0`) is `log (1 + L / (C - p - L))`, whose denominator
`C - p - L` is at least `C`; hence the increment is at most `log (1 + L / C)`, and
`log_one_add_div_le` finishes. -/
theorem G_left_le (C L p : ℝ) (hC : 0 < C) (hL : 0 ≤ L) (hp : p ≤ -L) :
    G C (p + L) - G C p ≤ 2 * Real.log (1 + L / (2 * C)) := by
  have hp0 : p ≤ 0 := by linarith
  have hpL0 : p + L ≤ 0 := by linarith
  rw [G_of_nonpos C (p + L) hC hpL0, G_of_nonpos C p hC hp0]
  have hA : (0 : ℝ) < 1 + -p / C := by
    have : 0 ≤ -p / C := div_nonneg (by linarith) (le_of_lt hC)
    linarith
  have hB : (0 : ℝ) < 1 + -(p + L) / C := by
    have : 0 ≤ -(p + L) / C := div_nonneg (by linarith) (le_of_lt hC)
    linarith
  have hC0 : C ≠ 0 := ne_of_gt hC
  have h2 : C - p - L ≠ 0 := by linarith
  -- the quotient of the two arguments is `1 + L / (C - p - L)`
  have hratio : (1 + -p / C) / (1 + -(p + L) / C) = 1 + L / (C - p - L) := by
    have hA' : 1 + -p / C = (C + -p) / C := by field_simp
    have hB' : 1 + -(p + L) / C = (C - p - L) / C := by field_simp; ring
    rw [hA', hB', div_div_div_cancel_right₀ hC0]
    rw [show C + -p = C - p by ring]
    rw [div_eq_iff h2]
    field_simp; ring
  -- `log A - log B = log (A / B)`
  have hlog : Real.log (1 + -p / C) - Real.log (1 + -(p + L) / C)
      = Real.log (1 + L / (C - p - L)) := by
    rw [← Real.log_div (ne_of_gt hA) (ne_of_gt hB), hratio]
  -- the denominator `C - p - L` is at least `C`
  have hCpL : C ≤ C - p - L := by linarith
  have hfrac : L / (C - p - L) ≤ L / C := div_le_div_of_nonneg_left hL hC hCpL
  have hlogpos : 0 < 1 + L / (C - p - L) := by
    have : 0 ≤ L / (C - p - L) := div_nonneg hL (by linarith)
    linarith
  have hle : 1 + L / (C - p - L) ≤ 1 + L / C := by linarith
  -- reorder the two logarithms into the difference `log A - log B`
  have hthis : -(Real.log (1 + -(p + L) / C)) - -(Real.log (1 + -p / C))
      = Real.log (1 + -p / C) - Real.log (1 + -(p + L) / C) := by ring
  rw [hthis, hlog]
  exact le_trans (Real.log_le_log hlogpos hle) (log_one_add_div_le C L hC hL)

end Work.Pert.PinLogDev
