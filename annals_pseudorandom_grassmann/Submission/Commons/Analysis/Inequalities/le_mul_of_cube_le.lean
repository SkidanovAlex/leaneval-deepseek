import Mathlib

namespace Commons.Analysis.Inequalities

theorem le_mul_of_cube_le {A B K X : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hX : 0 ≤ X)
    (h : A ^ 3 ≤ K * B ^ 3) (hKX : K ≤ X ^ 3) : A ≤ X * B := by
  have hb3 : 0 ≤ B ^ 3 := pow_nonneg hB 3
  have h1 : A ^ 3 ≤ (X * B) ^ 3 := by
    calc A ^ 3 ≤ K * B ^ 3 := h
      _ ≤ X ^ 3 * B ^ 3 := mul_le_mul_of_nonneg_right hKX hb3
      _ = (X * B) ^ 3 := by rw [mul_pow]
  exact (Odd.pow_le_pow (show Odd 3 by norm_num)).mp h1

end Commons.Analysis.Inequalities
