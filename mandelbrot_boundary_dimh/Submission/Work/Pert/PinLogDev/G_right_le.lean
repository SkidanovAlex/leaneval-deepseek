import Mathlib
import Submission.Work.Pert.PinLogDev.Prim

namespace Work.Pert.PinLogDev

/-- Right case of the primitive comparison: when the left endpoint `p` is nonnegative the whole
interval `[p, p + L]` lies on the nonnegative half-line, so

  `G C (p + L) - G C p = log (1 + (p + L) / C) - log (1 + p / C)
                       = log (1 + L / (C + p)) ≤ log (1 + L / C)`,

and `log (1 + L / C) ≤ 2 * log (1 + L / (2 * C))` is `log_one_add_div_le`. -/
theorem G_right_le (C L p : ℝ) (hC : 0 < C) (hL : 0 ≤ L) (hp : 0 ≤ p) :
    G C (p + L) - G C p ≤ 2 * Real.log (1 + L / (2 * C)) := by
  have hpL : 0 ≤ p + L := by linarith
  rw [G_of_nonneg C (p + L) hC hpL, G_of_nonneg C p hC hp]
  have h1 : 0 < 1 + p / C := by positivity
  have h2 : 0 < 1 + (p + L) / C := by positivity
  have h3 : 0 < 1 + L / C := by positivity
  -- `(1 + (p + L)/C) ≤ (1 + L/C) * (1 + p/C)`, the gap being `L * p / C^2 ≥ 0`.
  have hprod : 1 + (p + L) / C ≤ (1 + L / C) * (1 + p / C) := by
    have hkey : (1 + L / C) * (1 + p / C) - (1 + (p + L) / C) = L * p / C ^ 2 := by
      field_simp
      ring
    rw [← sub_nonneg, hkey]
    positivity
  have hlog : Real.log (1 + (p + L) / C) ≤ Real.log ((1 + L / C) * (1 + p / C)) :=
    Real.log_le_log h2 hprod
  rw [Real.log_mul (ne_of_gt h3) (ne_of_gt h1)] at hlog
  have hstep : Real.log (1 + (p + L) / C) - Real.log (1 + p / C) ≤ Real.log (1 + L / C) := by
    linarith
  exact le_trans hstep (log_one_add_div_le C L hC hL)

end Work.Pert.PinLogDev
