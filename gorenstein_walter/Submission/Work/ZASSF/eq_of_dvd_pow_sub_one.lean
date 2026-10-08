import Mathlib

namespace Work.ZASSF

/-- If `p` is an odd prime and `(p ^ k - 1) / 2` divides `p ^ m - 1` with `m ≤ k`,
then `m = k`. -/
theorem eq_of_dvd_pow_sub_one {p k m : ℕ} (hp : p.Prime) (hpodd : Odd p) (hk : 1 ≤ k) (hm : 1 ≤ m) (hmk : m ≤ k) (hdvd : (p ^ k - 1) / 2 ∣ p ^ m - 1) : m = k := by
  -- `p` is an odd prime, hence `p ≥ 3`.
  have hpne2 : p ≠ 2 := fun h => by rw [h] at hpodd; exact absurd hpodd (by norm_num)
  have hp2 : 2 < p := by have := hp.two_le; omega
  have hp3 : 3 ≤ p := by omega
  -- `p ^ k` is odd, so `p ^ k - 1` is even and `2 * ((p ^ k - 1) / 2) = p ^ k - 1`.
  have hodd : Odd (p ^ k) := hpodd.pow
  have hdiv : 2 ∣ p ^ k - 1 := by
    obtain ⟨t, ht⟩ := hodd
    exact ⟨t, by omega⟩
  have hd2 : 2 * ((p ^ k - 1) / 2) = p ^ k - 1 := Nat.mul_div_cancel' hdiv
  -- `p ^ m - 1 > 0`.
  have h3m : 3 ≤ p ^ m := by
    have a : 3 ≤ 3 ^ m := by simpa using Nat.pow_le_pow_right (show 0 < 3 by norm_num) hm
    exact le_trans a (Nat.pow_le_pow_left hp3 m)
  have hpm : 0 < p ^ m - 1 := by omega
  -- Hence `(p ^ k - 1) / 2 ≤ p ^ m - 1`, giving `p ^ k < 2 * p ^ m`.
  have hdle : (p ^ k - 1) / 2 ≤ p ^ m - 1 := Nat.le_of_dvd hpm hdvd
  have hlt : p ^ k < 2 * p ^ m := by omega
  -- Suppose `m < k`; then `p ^ k ≥ p ^ (m + 1) = p ^ m * p > 2 * p ^ m`, a contradiction.
  by_contra hne
  have hkm : m + 1 ≤ k := by omega
  have hle : p ^ (m + 1) ≤ p ^ k := Nat.pow_le_pow_right (by omega : 0 < p) hkm
  rw [pow_succ] at hle
  have hpmpos : 0 < p ^ m := Nat.pow_pos (by omega : 0 < p)
  have h2 : 2 * p ^ m < p ^ m * p := by
    calc 2 * p ^ m = p ^ m * 2 := Nat.mul_comm 2 (p ^ m)
      _ < p ^ m * p := Nat.mul_lt_mul_of_pos_left hp2 hpmpos
  omega

end Work.ZASSF
