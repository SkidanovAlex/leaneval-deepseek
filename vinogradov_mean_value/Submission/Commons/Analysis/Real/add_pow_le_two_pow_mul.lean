import Mathlib

namespace Commons.Analysis.Real

theorem add_pow_le_two_pow_mul (a b : ℝ) (n : ℕ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (a + b) ^ n ≤ (2 : ℝ) ^ n * (a ^ n + b ^ n) := by
  let m : ℝ := max a b
  have hm : 0 ≤ m := le_trans ha (le_max_left a b)
  have h1 : a + b ≤ 2 * m := by
    dsimp [m]
    nlinarith [le_max_left a b, le_max_right a b]
  have hnonneg : 0 ≤ a + b := add_nonneg ha hb
  have h2 : (a + b) ^ n ≤ (2 * m) ^ n := pow_le_pow_left₀ hnonneg h1 n
  have hmaxpow : m ^ n ≤ a ^ n + b ^ n := by
    dsimp [m]
    by_cases hab : a ≤ b
    · rw [max_eq_right hab]
      exact le_add_of_nonneg_left (pow_nonneg ha n)
    · have hba : b ≤ a := le_of_not_ge hab
      rw [max_eq_left hba]
      exact le_add_of_nonneg_right (pow_nonneg hb n)
  calc
    (a + b) ^ n ≤ (2 * m) ^ n := h2
    _ = (2 : ℝ) ^ n * m ^ n := by rw [mul_pow]
    _ ≤ (2 : ℝ) ^ n * (a ^ n + b ^ n) := by
      exact mul_le_mul_of_nonneg_left hmaxpow (pow_nonneg (by norm_num) n)

end Commons.Analysis.Real
