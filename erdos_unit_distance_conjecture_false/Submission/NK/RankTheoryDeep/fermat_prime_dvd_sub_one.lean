import Mathlib

namespace NK.RankTheoryDeep

/-- **The `2`-adic valuation of a Fermat prime divisor.**

If a prime `p` divides the Fermat number `2 ^ 2 ^ n + 1`, then `2 ^ (n + 1) ∣ p - 1`.

Indeed `2 ^ (2 ^ n) ≡ -1 (mod p)`, so `2 ^ (2 ^ (n+1)) ≡ 1` and `2 ^ (2 ^ n) ≠ 1`
(here `p` is odd, whence `2` is invertible); hence the multiplicative order of `2`
in `(ZMod p)ˣ` is exactly `2 ^ (n + 1)`, and it divides the order `p - 1` of that
group by Lagrange's theorem. -/
theorem fermat_prime_dvd_sub_one {n p : ℕ} (hp : p.Prime) (h : p ∣ 2 ^ 2 ^ n + 1) :
    2 ^ (n + 1) ∣ p - 1 := by
  have : Fact p.Prime := ⟨hp⟩
  -- `p` is odd: otherwise `2` would divide the odd number `2 ^ 2 ^ n + 1`.
  have hp2 : p ≠ 2 := by
    rintro rfl
    have h2dvd : 2 ∣ 2 ^ 2 ^ n := by
      have hpos : 0 < 2 ^ n := pow_pos (by norm_num) n
      exact ⟨2 ^ (2 ^ n - 1), by rw [← pow_succ']; congr 1; omega⟩
    have : 2 ∣ 1 := by simpa using Nat.dvd_sub h h2dvd
    exact Nat.prime_two.not_dvd_one this
  -- hence `2` is a unit in `ZMod p`.
  have h2ne : (2 : ZMod p) ≠ 0 := by
    intro h0
    have h02 : ((2 : ℕ) : ZMod p) = 0 := h0
    rw [ZMod.natCast_eq_zero_iff] at h02
    rcases (Nat.dvd_prime Nat.prime_two).mp h02 with h1 | h1
    · exact hp.ne_one h1
    · exact hp2 h1
  set u : (ZMod p)ˣ := Units.mk0 (2 : ZMod p) h2ne with hu
  have huval : (u : ZMod p) = 2 := by rw [hu, Units.val_mk0]
  -- `2 ^ (2 ^ n) = -1` in `ZMod p`.
  have hroot : (2 : ZMod p) ^ (2 ^ n) = -1 := by
    have h0 : ((2 ^ 2 ^ n + 1 : ℕ) : ZMod p) = 0 := by
      rw [ZMod.natCast_eq_zero_iff]; exact h
    push_cast at h0
    exact eq_neg_of_add_eq_zero_left h0
  have hu_pow : u ^ (2 ^ n) = -1 := by
    ext
    rw [Units.val_pow_eq_pow_val, huval]
    simpa using hroot
  -- squaring gives `u ^ (2 ^ (n+1)) = 1`.
  have hu_pow2 : u ^ (2 ^ (n + 1)) = 1 := by
    have hpow : 2 ^ (n + 1) = 2 ^ n * 2 := pow_succ 2 n
    rw [hpow, pow_mul, hu_pow]
    ext
    simp
  -- but `u ^ (2 ^ n) = -1 ≠ 1` since `2 ≠ 0` in `ZMod p`.
  have h1ne : (u ^ (2 ^ n)) ≠ 1 := by
    rw [hu_pow]
    intro hcontra
    have h1 : (-1 : ZMod p) = 1 := by
      have := congrArg (fun x : (ZMod p)ˣ => (x : ZMod p)) hcontra
      simpa using this
    have hh : (-1 : ZMod p) + 1 = 1 + 1 := congrArg (fun t : ZMod p => t + 1) h1
    rw [neg_add_cancel] at hh
    have h2zero : (2 : ZMod p) = 0 := by
      calc (2 : ZMod p) = 1 + 1 := by ring
        _ = 0 := hh.symm
    exact h2ne h2zero
  have hdvd : orderOf u ∣ 2 ^ (n + 1) := orderOf_dvd_of_pow_eq_one hu_pow2
  have hnotdvd : ¬ (orderOf u ∣ 2 ^ n) := by
    rw [orderOf_dvd_iff_pow_eq_one]
    exact h1ne
  -- a divisor of `2 ^ (n+1)` which does not divide `2 ^ n` equals `2 ^ (n+1)`.
  obtain ⟨k, hk_le, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
  have hkgt : n < k := by
    by_contra hle
    push Not at hle
    exact hnotdvd (by rw [hk]; exact pow_dvd_pow 2 hle)
  have hk_eq : k = n + 1 := by omega
  have horder : orderOf u = 2 ^ (n + 1) := by rw [hk, hk_eq]
  -- Lagrange: the order of an element divides the order `p - 1` of `(ZMod p)ˣ`.
  have hcard : orderOf u ∣ Fintype.card (ZMod p)ˣ := orderOf_dvd_card
  rw [ZMod.card_units p] at hcard
  rw [← horder]
  exact hcard

end NK.RankTheoryDeep
