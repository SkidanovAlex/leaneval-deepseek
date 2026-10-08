import Mathlib

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.Higman.Q3

/-- For `2 ≤ x` and `0 < m`, `x ^ m - 1` divides `x ^ k - 1` if and only if `m ∣ k`.  (The
forward direction is the one needed for the dimension argument in Higman's Lemma 11: with
`x = 2` it says that `2 ^ n - 1 ∣ 2 ^ d - 1` forces `n ∣ d`.) -/
theorem pow_sub_one_dvd_pow_sub_one_iff {x m k : ℕ} (hx : 2 ≤ x) (hm : 0 < m) :
    x ^ m - 1 ∣ x ^ k - 1 ↔ m ∣ k := by
  constructor
  · -- Forward direction: use `Nat.gcd (x ^ m - 1) (x ^ k - 1) = x ^ gcd m k - 1`.
    intro h
    have hgcd : Nat.gcd (x ^ m - 1) (x ^ k - 1) = x ^ m - 1 := Nat.gcd_eq_left h
    rw [Nat.pow_sub_one_gcd_pow_sub_one] at hgcd
    have h1 : 1 ≤ x ^ m := Nat.one_le_pow m x (by omega)
    have h2 : 1 ≤ x ^ Nat.gcd m k := Nat.one_le_pow _ x (by omega)
    have hpow : x ^ Nat.gcd m k = x ^ m := by
      calc x ^ Nat.gcd m k = x ^ Nat.gcd m k - 1 + 1 := (Nat.sub_add_cancel h2).symm
        _ = x ^ m - 1 + 1 := by rw [hgcd]
        _ = x ^ m := Nat.sub_add_cancel h1
    have hmk : Nat.gcd m k = m := Nat.pow_right_injective hx hpow
    rw [← hmk]
    exact Nat.gcd_dvd_right m k
  · -- Backward direction: `m ∣ k` gives `x ^ m - 1 ∣ x ^ k - 1`.
    intro h
    exact Nat.pow_sub_one_dvd_pow_sub_one x h

end Work.Higman.Q3
