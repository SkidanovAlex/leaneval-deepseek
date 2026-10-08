import Mathlib

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.Higman.Q3

/-- For `n ≥ 1` and exponents `A, B, C, D < n`, the difference of two sums of
powers of two is strictly smaller in absolute value than `2 ^ n - 1`.  In fact it
lies between `2 - 2 ^ n` and `2 ^ n - 2`. -/
theorem abs_two_pow_sub_lt {n A B C D : ℕ} (hn : 1 ≤ n) (hA : A < n) (hB : B < n) (hC : C < n) (hD : D < n) :
    |(2 ^ A : ℤ) + 2 ^ B - 2 ^ C - 2 ^ D| < 2 ^ n - 1 := by
  -- `2 ^ n = 2 * 2 ^ (n - 1)` as integers, for `n ≥ 1`.
  have hpow : (2 : ℤ) ^ n = 2 * (2 : ℤ) ^ (n - 1) := by
    rw [← pow_succ', Nat.sub_add_cancel hn]
  -- Upper bound: each of `2 ^ A, 2 ^ B` is at most `2 ^ (n - 1)` and each of
  -- `2 ^ C, 2 ^ D` is at least `1`.
  have hupper : (2 : ℤ) ^ A + 2 ^ B - 2 ^ C - 2 ^ D < 2 ^ n - 1 := by
    have hA2 : (2 : ℤ) ^ A ≤ (2 : ℤ) ^ (n - 1) := by
      exact_mod_cast (Nat.pow_le_pow_right (by norm_num : (0:ℕ) < 2) (Nat.le_sub_one_of_lt hA) : 2 ^ A ≤ 2 ^ (n-1))
    have hB2 : (2 : ℤ) ^ B ≤ (2 : ℤ) ^ (n - 1) := by
      exact_mod_cast (Nat.pow_le_pow_right (by norm_num : (0:ℕ) < 2) (Nat.le_sub_one_of_lt hB) : 2 ^ B ≤ 2 ^ (n-1))
    have hC1 : (1 : ℤ) ≤ (2 : ℤ) ^ C := one_le_pow₀ (by norm_num)
    have hD1 : (1 : ℤ) ≤ (2 : ℤ) ^ D := one_le_pow₀ (by norm_num)
    linarith
  -- Lower bound: each of `2 ^ C, 2 ^ D` is at most `2 ^ (n - 1)` and each of
  -- `2 ^ A, 2 ^ B` is at least `1`.
  have hlower : -(2 ^ n - 1) < (2 : ℤ) ^ A + 2 ^ B - 2 ^ C - 2 ^ D := by
    have hC2 : (2 : ℤ) ^ C ≤ (2 : ℤ) ^ (n - 1) := by
      exact_mod_cast (Nat.pow_le_pow_right (by norm_num : (0:ℕ) < 2) (Nat.le_sub_one_of_lt hC) : 2 ^ C ≤ 2 ^ (n-1))
    have hD2 : (2 : ℤ) ^ D ≤ (2 : ℤ) ^ (n - 1) := by
      exact_mod_cast (Nat.pow_le_pow_right (by norm_num : (0:ℕ) < 2) (Nat.le_sub_one_of_lt hD) : 2 ^ D ≤ 2 ^ (n-1))
    have hA1 : (1 : ℤ) ≤ (2 : ℤ) ^ A := one_le_pow₀ (by norm_num)
    have hB1 : (1 : ℤ) ≤ (2 : ℤ) ^ B := one_le_pow₀ (by norm_num)
    linarith
  rw [abs_lt]
  exact ⟨hlower, hupper⟩

end Work.Higman.Q3
