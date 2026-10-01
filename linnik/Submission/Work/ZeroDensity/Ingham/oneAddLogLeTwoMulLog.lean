import Mathlib

namespace Work.ZeroDensity.Ingham

theorem oneAddLogLeTwoMulLog (N : ℕ) (hN : 2 ≤ N) :
    1 + Real.log (N : ℝ) ≤ 2 * Real.log (2 * (N : ℝ)) := by
  have hN2 : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hpos : (0 : ℝ) < (N : ℝ) := by linarith
  have hlog2 : (1 / 2 : ℝ) ≤ Real.log 2 := by
    have := Real.log_two_gt_d9
    linarith
  have hlogN : (1 / 2 : ℝ) ≤ Real.log (N : ℝ) := by
    have h := Real.log_le_log (by norm_num : (0 : ℝ) < 2) hN2
    linarith
  have hmul : Real.log (2 * (N : ℝ)) = Real.log 2 + Real.log (N : ℝ) :=
    Real.log_mul (by norm_num) (by linarith)
  rw [hmul]
  nlinarith

end Work.ZeroDensity.Ingham
