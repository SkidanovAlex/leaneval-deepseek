import Mathlib

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.Higman.Q3.L12

/-- If `2^k + 2^l ≡ 2 [MOD 2^n - 1]` with `k, l < n` and `n ≥ 2`, then `k = l = 0`.

The key point is the size bound: since `k, l < n` we have `2^k, 2^l ≤ 2^(n-1)`, hence
`2 ≤ 2^k + 2^l ≤ 2^n`, so `0 ≤ 2^k + 2^l - 2 ≤ 2^n - 2 < 2^n - 1`. The congruence says
`2^n - 1 ∣ 2^k + 2^l - 2`, and a positive divisor of a smaller nonnegative number must be
`0`; thus `2^k + 2^l = 2` and both powers must equal `1`. -/
theorem res_ab_ab {n k l : ℕ} (hn : 2 ≤ n) (hk : k < n) (hl : l < n)
    (h : 2 ^ k + 2 ^ l ≡ 2 [MOD 2 ^ n - 1]) : k = 0 ∧ l = 0 := by
  have hpow4 : 4 ≤ 2 ^ n := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  -- Size bound: `2^k + 2^l ≤ 2^n`.
  have hsn : 2 ^ k + 2 ^ l ≤ 2 ^ n := by
    have h1 : 2 ^ k ≤ 2 ^ (n - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have h2 : 2 ^ l ≤ 2 ^ (n - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have h3 : 2 ^ (n - 1) * 2 = 2 ^ n := by
      rw [← pow_succ]; congr 1; omega
    have h4 : 2 ^ n = 2 ^ (n - 1) + 2 ^ (n - 1) := by
      rw [← h3]; ring
    omega
  have hsge2 : 2 ≤ 2 ^ k + 2 ^ l := by
    have h1 := Nat.one_le_two_pow (n := k)
    have h2 := Nat.one_le_two_pow (n := l)
    omega
  -- `0 ≤ 2^k + 2^l - 2 < 2^n - 1`.
  have hs2lt : 2 ^ k + 2 ^ l - 2 < 2 ^ n - 1 := by omega
  -- The congruence, made explicit.
  have hmod : (2 ^ k + 2 ^ l) % (2 ^ n - 1) = 2 := by
    have h2 : 2 % (2 ^ n - 1) = 2 := Nat.mod_eq_of_lt (by omega)
    have hh := h
    rw [Nat.ModEq, h2] at hh
    exact hh
  -- Divisibility.
  have hdvd : (2 ^ n - 1) ∣ (2 ^ k + 2 ^ l - 2) := by
    have hh := Nat.dvd_sub_mod (n := 2 ^ n - 1) (2 ^ k + 2 ^ l)
    rwa [hmod] at hh
  have hzero : 2 ^ k + 2 ^ l - 2 = 0 := Nat.eq_zero_of_dvd_of_lt hdvd hs2lt
  have hsum : 2 ^ k + 2 ^ l = 2 := by omega
  constructor
  · by_contra hk0
    have hk1 : 1 ≤ k := by omega
    have h2k : 2 ≤ 2 ^ k := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk1
    have h1 := Nat.one_le_two_pow (n := l)
    omega
  · by_contra hl0
    have hl1 : 1 ≤ l := by omega
    have h2l : 2 ≤ 2 ^ l := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ l := Nat.pow_le_pow_right (by norm_num) hl1
    have h1 := Nat.one_le_two_pow (n := k)
    omega

end Work.Higman.Q3.L12
