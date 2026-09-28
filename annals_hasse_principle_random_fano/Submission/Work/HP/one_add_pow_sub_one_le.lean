import Mathlib

namespace Work.HP

theorem one_add_pow_sub_one_le (N : ℕ) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    (1 + t) ^ N - 1 ≤ (2 : ℝ) ^ N * t := by
  -- Stronger statement: (1+t)^N ≤ 1 + (2^N - 1) * t for t ∈ [0,1].
  have key : ∀ N : ℕ, (1 + t) ^ N ≤ 1 + ((2 : ℝ) ^ N - 1) * t := by
    intro N
    induction N with
    | zero => simp
    | succ n ih =>
      have h1t : (0 : ℝ) ≤ 1 + t := by linarith
      have h2n : (1 : ℝ) ≤ (2 : ℝ) ^ n := one_le_pow₀ (by norm_num)
      have ht2 : t ^ 2 ≤ t := by nlinarith [mul_le_mul_of_nonneg_right ht1 ht0]
      have hpow : (2 : ℝ) ^ (n + 1) = 2 * (2 : ℝ) ^ n := by rw [pow_succ]; ring
      calc (1 + t) ^ (n + 1) = (1 + t) ^ n * (1 + t) := by rw [pow_succ]
        _ ≤ (1 + ((2 : ℝ) ^ n - 1) * t) * (1 + t) :=
              mul_le_mul_of_nonneg_right ih h1t
        _ ≤ 1 + ((2 : ℝ) ^ (n + 1) - 1) * t := by
              nlinarith [hpow, h2n, ht2, ht0]
  have hfin : ((2 : ℝ) ^ N - 1) * t ≤ (2 : ℝ) ^ N * t := by
    have : (2 : ℝ) ^ N - 1 ≤ (2 : ℝ) ^ N := by norm_num
    exact mul_le_mul_of_nonneg_right this ht0
  linarith [key N, hfin]

end Work.HP
