import Mathlib

namespace Work.Fx

/-- `exp (2 * log 2) = 4`, since `2 * log 2 = log 4`. -/
lemma exp_two_log_two : Real.exp (2 * Real.log 2) = 4 := by
  have hlog4 : Real.log 4 = 2 * Real.log 2 := by
    have h := Real.log_pow (2 : ℝ) 2
    norm_num at h
    exact h
  rw [← hlog4]
  exact Real.exp_log (by norm_num)

theorem expSubSmall (y z : ℝ) (hy : y ≤ 2 * Real.log 2) (hzy : |z - y| ≤ 1) :
    |Real.exp z - Real.exp y| ≤ 8 * |z - y| := by
  -- `exp y ≤ 4`
  have hy4 : Real.exp y ≤ 4 := by
    rw [← exp_two_log_two]
    exact Real.exp_le_exp.mpr hy
  -- `exp z = exp y * exp (z - y)`
  have hexpz : Real.exp z = Real.exp y * Real.exp (z - y) := by
    have h := Real.exp_sub z y
    rw [h]
    field_simp
  have hfact : Real.exp y * Real.exp (z - y) - Real.exp y
      = Real.exp y * (Real.exp (z - y) - 1) := by ring
  calc |Real.exp z - Real.exp y|
      = Real.exp y * |Real.exp (z - y) - 1| := by
          rw [hexpz, hfact, abs_mul, abs_of_pos (Real.exp_pos y)]
    _ ≤ Real.exp y * (2 * |z - y|) :=
          mul_le_mul_of_nonneg_left (Real.abs_exp_sub_one_le hzy) (Real.exp_pos y).le
    _ ≤ 4 * (2 * |z - y|) := by
          apply mul_le_mul_of_nonneg_right hy4; positivity
    _ = 8 * |z - y| := by ring

end Work.Fx
