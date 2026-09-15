import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Submission.Commons.Analysis.ExpLog.atanh_series_log_lower

namespace Commons.Analysis.Real

/-- The arithmetic–harmonic–logarithmic lower bound `2(x-1)/(x+1) ≤ log x`
for `x ≥ 1`, obtained from the first term of the artanh series expansion of
`log ((1+r)/(1-r))` at `r = (x-1)/(x+1)`. -/
theorem two_mul_sub_div_add_le_log {x : ℝ} (hx : 1 ≤ x) :
    2 * (x - 1) / (x + 1) ≤ Real.log x := by
  rcases eq_or_lt_of_le hx with h | h
  · subst h
    norm_num [Real.log_one]
  · have hz : (0:ℝ) < x - 1 := by linarith
    have hx1 : (0:ℝ) < x + 1 := by linarith
    have hr0 : (0:ℝ) < (x - 1) / (x + 1) := div_pos hz hx1
    have hr1 : (x - 1) / (x + 1) < 1 := by
      rw [div_lt_one hx1]
      linarith
    have h :=
      Commons.Analysis.ExpLog.atanh_series_log_lower hr0 hr1 0
    have hsum : (Finset.sum (Finset.range (0 + 1))
        (fun k => ((x - 1) / (x + 1)) ^ (2 * k + 1) / (2 * k + 1 : ℝ)))
        = (x - 1) / (x + 1) := by
      simp
    rw [hsum] at h
    have harg : (1 + (x - 1) / (x + 1)) / (1 - (x - 1) / (x + 1)) = x := by
      have hx1' : x + 1 ≠ 0 := ne_of_gt hx1
      field_simp
      ring
    rw [harg] at h
    calc 2 * (x - 1) / (x + 1)
        = 2 * ((x - 1) / (x + 1)) := by ring
      _ ≤ Real.log x := h

end Commons.Analysis.Real
