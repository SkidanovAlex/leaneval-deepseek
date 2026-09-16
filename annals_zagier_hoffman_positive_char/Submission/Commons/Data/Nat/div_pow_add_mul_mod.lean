import Mathlib.Data.Nat.ModEq

/-!
# A base-`p` digit computation

For `p ≥ 2`, `a < p ^ k` and any `c`, the number `p ^ k * c + a` has base-`p`
expansion obtained by concatenating the expansion of `c` with the `k` low-order
digits of the expansion of `a`.  Consequently its `i`-th base-`p` digit is the
`i`-th digit of `a` when `i < k`, and the `(i - k)`-th digit of `c` otherwise.

This is the elementary arithmetic fact underlying the analysis of the
Zagier–Hoffman conjectures in positive characteristic, where one reads off the
digits of a polynomial's value in a power series expansion.
-/

namespace Commons.Data.Nat

/-- The `i`-th base-`p` digit of `(p ^ k * c + a) / p ^ i` (`i < k` case):
`p ^ i` divides `p ^ k * c` and the quotient is `p ^ (k - i) * c`. -/
theorem pow_mul_div_pow (p k i c : ℕ) (hp : 0 < p) (h : i ≤ k) :
    p ^ k * c / p ^ i = p ^ (k - i) * c := by
  rw [← pow_sub_mul_pow p h, mul_assoc]
  rw [Nat.mul_div_assoc _ (dvd_mul_right _ _), Nat.mul_div_right _ (Nat.pow_pos hp)]

theorem div_pow_add_mul_mod (p k : ℕ) (hp : 2 ≤ p) {a c : ℕ} (ha : a < p ^ k) (i : ℕ) :
    (p ^ k * c + a) / p ^ i % p = if i < k then a / p ^ i % p else c / p ^ (i - k) % p := by
  have hp0 : 0 < p := by omega
  have hpk0 : 0 < p ^ k := Nat.pow_pos hp0
  rcases lt_or_ge i k with hik | hki
  · -- low-order digits: `i < k`
    rw [if_pos hik]
    have hle : i ≤ k := le_of_lt hik
    have hmod0 : p ^ (k - i) * c % p = 0 := by
      apply Nat.mod_eq_zero_of_dvd
      exact dvd_mul_of_dvd_left (by simpa using Nat.pow_dvd_pow p (Nat.sub_pos_of_lt hik)) c
    rw [Nat.add_comm (p ^ k * c) a,
      Nat.add_div_of_dvd_left (dvd_mul_of_dvd_left (Nat.pow_dvd_pow p hle) c),
      pow_mul_div_pow p k i c hp0 hle]
    rw [Nat.add_mod, hmod0, Nat.add_zero, Nat.mod_mod]
  · -- high-order digits: `k ≤ i`
    rw [if_neg (not_lt.mpr hki)]
    have hpi : p ^ i = p ^ k * p ^ (i - k) := by
      rw [← Nat.pow_add, Nat.add_sub_cancel' hki]
    rw [hpi, ← Nat.div_div_eq_div_mul, Nat.mul_add_div hpk0, Nat.div_eq_of_lt ha, Nat.add_zero]

end Commons.Data.Nat