import Mathlib

namespace Work.Motion

theorem arith_bound {R M d x : ℝ} (hR : 0 < R) (hM : 0 < M) (hd0 : 0 ≤ d) (hdR : d < R)
    (h : R / M * x ≤ 1 / (1 - (d / R) ^ 2)) :
    x ≤ M * R / (R ^ 2 - d ^ 2) := by
  have hsq : d ^ 2 < R ^ 2 := by
    nlinarith [sq_nonneg (R - d), sq_nonneg (R + d), hdR, hd0, hR]
  have hR2 : 0 < R ^ 2 - d ^ 2 := by nlinarith
  have hden : 0 < 1 - (d / R) ^ 2 := by
    have : (d / R) ^ 2 < 1 := by
      rw [div_pow, div_lt_one (by positivity)]
      exact hsq
    linarith
  calc x = (M / R) * (R / M * x) := by field_simp
    _ ≤ (M / R) * (1 / (1 - (d / R) ^ 2)) := by
        exact mul_le_mul_of_nonneg_left h (by positivity)
    _ = M * R / (R ^ 2 - d ^ 2) := by
        field_simp

end Work.Motion
