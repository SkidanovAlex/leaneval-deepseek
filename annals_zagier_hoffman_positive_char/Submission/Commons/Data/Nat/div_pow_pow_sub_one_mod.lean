import Mathlib.Algebra.Order.Group.Nat

set_option linter.unusedVariables false

/-!
# A base-`p` digit computation

For `2 ≤ p` and `1 ≤ k`, the quotient `(p ^ k - 1) / p ^ i` is the number whose
base-`p` expansion consists of the top `k - i` digits of `p ^ k - 1` shifted down,
so its last digit modulo `p` is `p - 1` when `i < k` and `0` otherwise.

These are the supporting facts used by `div_pow_pow_sub_one_mod`.
-/

namespace Commons.Data.Nat

/-- Dividing `p ^ n - 1` by `p` removes one trailing digit, i.e. subtracts `1`
from the exponent. -/
private theorem pow_sub_one_div_self (p n : ℕ) (hp : 1 ≤ p) (hn : 1 ≤ n) :
    (p ^ n - 1) / p = p ^ (n - 1) - 1 := by
  have hp0 : 0 < p := hp
  have hpn : p ^ n = p * p ^ (n - 1) := by
    conv_lhs => rw [← Nat.sub_add_cancel hn]
    rw [pow_succ, Nat.mul_comm]
  rw [hpn]
  have hsplit : p * p ^ (n - 1) - 1 = p * (p ^ (n - 1) - 1) + (p - 1) := by
    rw [Nat.mul_sub_left_distrib, Nat.mul_one]
    have hA : p ≤ p * p ^ (n - 1) := Nat.le_mul_of_pos_right p (Nat.pow_pos hp0)
    omega
  rw [hsplit, Nat.mul_add_div hp0]
  simp [Nat.div_eq_of_lt (show p - 1 < p by omega)]

/-- `p ^ n - 1` has last base-`p` digit `p - 1` (for `1 ≤ n`, `1 ≤ p`). -/
private theorem pow_sub_one_mod_self (p n : ℕ) (hp : 1 ≤ p) (hn : 1 ≤ n) :
    (p ^ n - 1) % p = p - 1 := by
  have hp0 : 0 < p := hp
  have hpn : p ^ n = p * p ^ (n - 1) := by
    conv_lhs => rw [← Nat.sub_add_cancel hn]
    rw [pow_succ, Nat.mul_comm]
  rw [hpn]
  have hsplit : p * p ^ (n - 1) - 1 = p * (p ^ (n - 1) - 1) + (p - 1) := by
    rw [Nat.mul_sub_left_distrib, Nat.mul_one]
    have hA : p ≤ p * p ^ (n - 1) := Nat.le_mul_of_pos_right p (Nat.pow_pos hp0)
    omega
  rw [hsplit, Nat.add_comm, Nat.add_mul_mod_self_left]
  exact Nat.mod_eq_of_lt (by omega)

/-- Dividing `p ^ k - 1` by `p ^ i` (with `i ≤ k`) subtracts `i` from the exponent. -/
private theorem pow_sub_one_div_pow (p k i : ℕ) (hp : 1 ≤ p) (hi : i ≤ k) :
    (p ^ k - 1) / p ^ i = p ^ (k - i) - 1 := by
  revert k
  induction i with
  | zero => intro k _; simp
  | succ i ih =>
    intro k hi
    have hik : i ≤ k := by omega
    have hpos : 1 ≤ k - i := by omega
    rw [pow_succ, ← Nat.div_div_eq_div_mul, ih k hik]
    rw [pow_sub_one_div_self p (k - i) hp hpos]
    rw [show k - i - 1 = k - (i + 1) by omega]

theorem div_pow_pow_sub_one_mod (p k : ℕ) (hp : 2 ≤ p) (hk : 1 ≤ k) (i : ℕ) :
    (p ^ k - 1) / p ^ i % p = if i < k then p - 1 else 0 := by
  rcases Nat.lt_or_ge i k with h | h
  · rw [if_pos h]
    have hp1 : 1 ≤ p := by omega
    have hi : i ≤ k := le_of_lt h
    rw [pow_sub_one_div_pow p k i hp1 hi]
    exact pow_sub_one_mod_self p (k - i) hp1 (by omega)
  · rw [if_neg (by omega)]
    have hp0 : 0 < p := by omega
    have hlt : p ^ k - 1 < p ^ i := by
      have hle : p ^ k ≤ p ^ i := Nat.pow_le_pow_right hp0 h
      exact lt_of_lt_of_le (Nat.sub_one_lt (Nat.pow_pos hp0).ne') hle
    rw [Nat.div_eq_of_lt hlt, Nat.zero_mod]

end Commons.Data.Nat