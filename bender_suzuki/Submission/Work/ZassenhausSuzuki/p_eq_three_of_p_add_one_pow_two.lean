import Mathlib
import Submission.Work.ZassenhausSuzuki.pow_two_defs

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.ZassenhausSuzuki

/-- Arithmetic step of the Zassenhaus–Suzuki argument.

If `p` is an odd prime, `p + 1 = 2 ^ j` and `p ∣ 2 ^ a + 1` for some `a`, then `p = 3`.

The proof works inside `ZMod p`: from `p + 1 = 2 ^ j` we get `2 ^ j = 1`, while
`p ∣ 2 ^ a + 1` gives `2 ^ a = -1`.  Hence `2 ^ (j * a) = (2 ^ j) ^ a = 1` and also
`2 ^ (j * a) = (2 ^ a) ^ j = (-1) ^ j`, so `(-1) ^ j = 1`.  For odd `j` this forces
`-1 = 1` in `ZMod p`, i.e. `p = 2`, contradicting the hypothesis; thus `j` is even.
Writing `j = 2 * k` we get `p = 2 ^ (2 * k) - 1 = (2 ^ k - 1) * (2 ^ k + 1)`.  Since
`p` is prime and both factors are positive, the factor `2 ^ k - 1` must be `1`, so
`2 ^ k = 2`, `k = 1`, `j = 2` and finally `p = 2 ^ 2 - 1 = 3`. -/
theorem p_eq_three_of_p_add_one_pow_two {p j a : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hj : p + 1 = 2 ^ j) (ha : p ∣ 2 ^ a + 1) : p = 3 := by
  have hpge : 2 ≤ p := hp.two_le
  -- `2 ^ j = 1` and `2 ^ a = -1` in `ZMod p`.
  have h2j : (2 : ZMod p) ^ j = 1 := by
    have h : ((2 ^ j : ℕ) : ZMod p) = 1 := by
      rw [← hj, Nat.cast_add, Nat.cast_one, ZMod.natCast_self, zero_add]
    rwa [Nat.cast_pow] at h
  have h2a : (2 : ZMod p) ^ a = -1 := by
    have h : ((2 ^ a + 1 : ℕ) : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff (2 ^ a + 1) p).mpr ha
    rw [Nat.cast_add, Nat.cast_one, Nat.cast_pow] at h
    exact eq_neg_of_add_eq_zero_left h
  -- `(-1) ^ j = 1`, hence `j` is even.
  have hpow : (-1 : ZMod p) ^ j = 1 := by
    have h1 : (2 : ZMod p) ^ (j * a) = 1 := by rw [pow_mul, h2j, one_pow]
    have h2 : (2 : ZMod p) ^ (j * a) = (-1) ^ j := by
      rw [mul_comm j a, pow_mul, h2a]
    exact h2.symm.trans h1
  have hjeven : Even j := by
    rw [← Nat.not_odd_iff_even]
    intro hodd
    rw [hodd.neg_one_pow] at hpow
    rcases ZMod.neg_one_eq_one_iff.mp hpow with h | h
    · exact absurd h hp.ne_one
    · exact absurd h hp2
  obtain ⟨k, hk⟩ := even_iff_two_dvd.mp hjeven
  have hjge : 3 ≤ 2 ^ j := hj ▸ (show 3 ≤ p + 1 by omega)
  have hj2 : 2 ≤ j := by
    by_contra h
    have h' : j < 2 := Nat.lt_of_not_le h
    have hle : 2 ^ j ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) (by omega)
    norm_num at hle
    omega
  have hk1 : 1 ≤ k := by omega
  have hpk : p + 1 = 2 ^ k * 2 ^ k := by
    rw [hj, hk, pow_mul', pow_two]
  have hp_eq : p = 2 ^ k * 2 ^ k - 1 := by omega
  have hident : (2 ^ k - 1) * (2 ^ k + 1) = 2 ^ k * 2 ^ k - 1 := by
    rw [mul_comm (2 ^ k - 1) (2 ^ k + 1)]
    exact (mul_self_tsub_one (2 ^ k)).symm
  have hprod : p = (2 ^ k - 1) * (2 ^ k + 1) := by
    rw [hp_eq]; exact hident.symm
  have hdiv : 2 ^ k - 1 ∣ p := ⟨2 ^ k + 1, hprod⟩
  rcases hp.eq_one_or_self_of_dvd (2 ^ k - 1) hdiv with h | h
  · -- `2 ^ k - 1 = 1`, so `k = 1`, `j = 2` and `p = 3`.
    have h2k2 : 2 ^ k = 2 := by omega
    have hk1' : k = 1 := by
      have : 2 ^ k = 2 ^ 1 := by simpa using h2k2
      exact Nat.pow_right_injective (by norm_num : 2 ≤ 2) this
    have hj2' : j = 2 := by rw [hk1'] at hk; omega
    rw [hj2'] at hj
    norm_num at hj
    omega
  · -- `2 ^ k - 1 = p` would force `p = p * (2 ^ k + 1)`, impossible.
    exfalso
    rw [h] at hprod
    have heq : p * 1 = p * (2 ^ k + 1) := by rw [mul_one]; exact hprod
    have hone : 1 = 2 ^ k + 1 := Nat.mul_left_cancel hp.pos heq
    have : 1 ≤ 2 ^ k := Nat.one_le_two_pow
    omega

end Work.ZassenhausSuzuki
