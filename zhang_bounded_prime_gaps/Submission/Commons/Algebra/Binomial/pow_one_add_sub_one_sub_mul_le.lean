import Mathlib.Algebra.Order.Star.Real

namespace Commons.Algebra.Binomial

/-- Auxiliary: `n ≤ 7 ^ n` for real natural casts. -/
private lemma nat_cast_le_seven_pow (n : ℕ) : (n : ℝ) ≤ (7 : ℝ) ^ n := by
  induction n with
  | zero => norm_num
  | succ n ih =>
    have h1 : (1 : ℝ) ≤ (7 : ℝ) ^ n := one_le_pow₀ (by norm_num)
    have h2 : (0 : ℝ) ≤ (7 : ℝ) ^ n := pow_nonneg (by norm_num) n
    have h3 : ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 := by push_cast; ring
    rw [h3]
    calc (n : ℝ) + 1 ≤ (7 : ℝ) ^ n + (7 : ℝ) ^ n := by linarith
      _ ≤ (7 : ℝ) ^ (n + 1) := by
            rw [pow_succ]; nlinarith

theorem pow_one_add_sub_one_sub_mul_le (n : ℕ) (r : ℝ) (hr : 0 ≤ r) (hr2 : r ≤ 7 / 2) :
    (1 + r) ^ n - 1 - (n : ℝ) * r ≤ (7 : ℝ) ^ n * r ^ 2 := by
  induction n with
  | zero =>
    have h : ((1 + r) ^ 0 - 1 - ((0 : ℕ) : ℝ) * r) = 0 := by norm_num
    have h2 : (7 : ℝ) ^ 0 * r ^ 2 = r ^ 2 := by norm_num
    rw [h, h2]
    exact sq_nonneg r
  | succ n ih =>
    have hrpow : (0 : ℝ) ≤ r ^ 2 := sq_nonneg r
    have h7n : (0 : ℝ) ≤ (7 : ℝ) ^ n := pow_nonneg (by norm_num) n
    have hkey : (1 + r) ^ (n + 1) - 1 - ((n + 1 : ℕ) : ℝ) * r
        = (1 + r) * ((1 + r) ^ n - 1 - (n : ℝ) * r) + (n : ℝ) * r ^ 2 := by
      rw [pow_succ]; push_cast; ring
    rw [hkey]
    have h1 : (1 + r) * ((1 + r) ^ n - 1 - (n : ℝ) * r)
        ≤ (1 + r) * ((7 : ℝ) ^ n * r ^ 2) :=
      mul_le_mul_of_nonneg_left ih (by linarith)
    have h3 : (1 + r) * (7 : ℝ) ^ n + (n : ℝ) ≤ (7 : ℝ) ^ (n + 1) := by
      have hle6 : 1 + r ≤ 6 := by linarith
      have hn : (n : ℝ) ≤ (7 : ℝ) ^ n := nat_cast_le_seven_pow n
      calc (1 + r) * (7 : ℝ) ^ n + (n : ℝ)
          ≤ 6 * (7 : ℝ) ^ n + (7 : ℝ) ^ n := by
            have := mul_le_mul_of_nonneg_right hle6 h7n
            linarith
        _ = (7 : ℝ) ^ (n + 1) := by rw [pow_succ]; ring
    calc (1 + r) * ((1 + r) ^ n - 1 - (n : ℝ) * r) + (n : ℝ) * r ^ 2
        ≤ (1 + r) * ((7 : ℝ) ^ n * r ^ 2) + (n : ℝ) * r ^ 2 := by linarith
      _ = ((1 + r) * (7 : ℝ) ^ n + (n : ℝ)) * r ^ 2 := by ring
      _ ≤ (7 : ℝ) ^ (n + 1) * r ^ 2 := mul_le_mul_of_nonneg_right h3 hrpow

end Commons.Algebra.Binomial