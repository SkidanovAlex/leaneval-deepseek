import Mathlib

namespace Work.Resample

/-- `n ≤ 2 ^ n` for every natural number. -/
private lemma le_two_pow (n : ℕ) : n ≤ 2 ^ n := (Nat.lt_two_pow_self (n := n)).le

/-- A single term `a * B ^ k` of the cost polynomial is bounded by `2 ^ N * B ^ m`,
provided `a ≤ 2 ^ N`, `k ≤ 2 ^ N ≤ m` and `1 ≤ B`. -/
private lemma mul_pow_le (B a k m N : ℕ) (hB : 1 ≤ B) (ha : a ≤ 2 ^ N) (hk : k ≤ 2 ^ N)
    (hm : 2 ^ N ≤ m) : a * B ^ k ≤ 2 ^ N * B ^ m := by
  have hkm : k ≤ m := le_trans hk hm
  have hpow : B ^ k ≤ B ^ m := pow_le_pow_right₀ hB hkm
  calc a * B ^ k ≤ 2 ^ N * B ^ k := Nat.mul_le_mul_right _ ha
    _ ≤ 2 ^ N * B ^ m := Nat.mul_le_mul_left _ hpow

theorem auCostSum (c1 c2 c3 c4 K2 K3 K4 p : ℕ) :
    c1 + (c2 * (p + 1) ^ K2 + (c3 * (p + 1) ^ K3 + c4 * (p + 1) ^ K4)) ≤
      (2 ^ (c1 + c2 + c3 + c4 + K2 + K3 + K4 + 20)) *
        (p + 1) ^ (2 ^ (c1 + c2 + c3 + c4 + K2 + K3 + K4 + 20)) := by
  -- Abbreviate the total size `N` of the coefficients/exponents and the base `B = p + 1`.
  let N := c1 + c2 + c3 + c4 + K2 + K3 + K4
  let B := p + 1
  show c1 + (c2 * B ^ K2 + (c3 * B ^ K3 + c4 * B ^ K4)) ≤
    2 ^ (N + 20) * B ^ (2 ^ (N + 20))
  have hB1 : 1 ≤ B := by omega
  have hN : N ≤ 2 ^ N := le_two_pow N
  -- Every coefficient and exponent is at most `N ≤ 2 ^ N`.
  have hc1 : c1 ≤ 2 ^ N := le_trans (by omega) hN
  have hc2 : c2 ≤ 2 ^ N := le_trans (by omega) hN
  have hc3 : c3 ≤ 2 ^ N := le_trans (by omega) hN
  have hc4 : c4 ≤ 2 ^ N := le_trans (by omega) hN
  have hK2 : K2 ≤ 2 ^ N := le_trans (by omega) hN
  have hK3 : K3 ≤ 2 ^ N := le_trans (by omega) hN
  have hK4 : K4 ≤ 2 ^ N := le_trans (by omega) hN
  have hm : 2 ^ N ≤ 2 ^ (N + 20) := Nat.pow_le_pow_right (by norm_num) (by omega)
  -- Each of the four summands is at most `2 ^ N * B ^ (2 ^ (N + 20))`.
  have hX1 : c1 ≤ 2 ^ N * B ^ (2 ^ (N + 20)) := by
    have h1 : 1 ≤ B ^ (2 ^ (N + 20)) := one_le_pow₀ hB1
    calc c1 ≤ 2 ^ N := hc1
      _ = 2 ^ N * 1 := (mul_one _).symm
      _ ≤ 2 ^ N * B ^ (2 ^ (N + 20)) := Nat.mul_le_mul_left _ h1
  have hX2 : c2 * B ^ K2 ≤ 2 ^ N * B ^ (2 ^ (N + 20)) :=
    mul_pow_le B c2 K2 (2 ^ (N + 20)) N hB1 hc2 hK2 hm
  have hX3 : c3 * B ^ K3 ≤ 2 ^ N * B ^ (2 ^ (N + 20)) :=
    mul_pow_le B c3 K3 (2 ^ (N + 20)) N hB1 hc3 hK3 hm
  have hX4 : c4 * B ^ K4 ≤ 2 ^ N * B ^ (2 ^ (N + 20)) :=
    mul_pow_le B c4 K4 (2 ^ (N + 20)) N hB1 hc4 hK4 hm
  have hsum := add_le_add hX1 (add_le_add hX2 (add_le_add hX3 hX4))
  -- Four copies of the bound, and `4 ≤ 2 ^ 20` absorbs them into the leading factor.
  have h4 : 2 ^ N * B ^ (2 ^ (N + 20)) +
      (2 ^ N * B ^ (2 ^ (N + 20)) + (2 ^ N * B ^ (2 ^ (N + 20)) + 2 ^ N * B ^ (2 ^ (N + 20))))
      = 4 * (2 ^ N * B ^ (2 ^ (N + 20))) := by ring
  have h2 : 4 * (2 ^ N * B ^ (2 ^ (N + 20))) ≤ 2 ^ 20 * (2 ^ N * B ^ (2 ^ (N + 20))) :=
    Nat.mul_le_mul_right _ (by norm_num)
  have hkey : 2 ^ 20 * (2 ^ N * B ^ (2 ^ (N + 20))) = 2 ^ (N + 20) * B ^ (2 ^ (N + 20)) := by
    rw [← mul_assoc, ← pow_add, Nat.add_comm]
  calc c1 + (c2 * B ^ K2 + (c3 * B ^ K3 + c4 * B ^ K4))
      ≤ 2 ^ N * B ^ (2 ^ (N + 20)) +
          (2 ^ N * B ^ (2 ^ (N + 20)) +
            (2 ^ N * B ^ (2 ^ (N + 20)) + 2 ^ N * B ^ (2 ^ (N + 20)))) := hsum
    _ = 4 * (2 ^ N * B ^ (2 ^ (N + 20))) := h4
    _ ≤ 2 ^ 20 * (2 ^ N * B ^ (2 ^ (N + 20))) := h2
    _ = 2 ^ (N + 20) * B ^ (2 ^ (N + 20)) := hkey

end Work.Resample
