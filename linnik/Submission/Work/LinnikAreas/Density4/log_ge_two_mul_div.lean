import Mathlib

namespace Work.LinnikAreas.Density4

/-- For `x ≥ 1`, the elementary lower bound `2(x-1)/(x+1) ≤ log x` for the logarithm. -/
lemma log_ge_two_mul_div {x : ℝ} (hx : 1 ≤ x) : 2*(x-1)/(x+1) ≤ Real.log x := by
  have h : 0 ≤ x - 1 := by linarith
  have hlog := Real.le_log_one_add_of_nonneg h
  rw [show (1:ℝ) + (x - 1) = x by ring, show (x - 1) + 2 = x + 1 by ring] at hlog
  exact hlog

end Work.LinnikAreas.Density4
