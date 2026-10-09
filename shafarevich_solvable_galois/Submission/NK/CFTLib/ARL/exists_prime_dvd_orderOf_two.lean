import Mathlib
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace NK.CFTLib.ARL

/-- For an odd natural number `x`, the number `(x ^ 2 + 1) / 2` is odd. -/
lemma odd_div_two_sq_add_one (x : ℕ) (hx : Odd x) : Odd ((x ^ 2 + 1) / 2) := by
  obtain ⟨k, rfl⟩ := hx
  have h : (2 * k + 1) ^ 2 + 1 = 2 * (2 * k ^ 2 + 2 * k + 1) := by ring
  rw [h, Nat.mul_div_right (2 * k ^ 2 + 2 * k + 1) (m := 2) (by norm_num)]
  exact ⟨k ^ 2 + k, by ring⟩

/-- For every odd `a ≥ 2` and every `E ≥ 1` there is a prime `p` with `p ∤ a`,
`2 ^ E ∣ orderOf (a mod p)` and `2 ^ E < p`. -/
theorem exists_prime_dvd_orderOf_two (a E : ℕ) (ha : 2 ≤ a) (hodd : Odd a) (hE : 1 ≤ E) :
    ∃ p : ℕ, p.Prime ∧ ¬ p ∣ a ∧ 2 ^ E ∣ orderOf ((a : ZMod p)) ∧ 2 ^ E < p := by
  have ha3 : 3 ≤ a := by obtain ⟨k, hk⟩ := hodd; omega
  -- `a ^ (2 ^ E)` is the square of the odd number `a ^ (2 ^ (E - 1))`
  have hsq : a ^ (2 ^ E) = (a ^ (2 ^ (E - 1))) ^ 2 := by
    rw [← pow_mul, show 2 ^ (E - 1) * 2 = 2 ^ E by rw [← pow_succ, Nat.sub_add_cancel hE]]
  have hEvenn : Even (a ^ (2 ^ E) + 1) := Odd.add_odd hodd.pow odd_one
  -- `(a ^ (2 ^ E) + 1) / 2` is odd, hence bigger than one, hence has an odd prime factor
  have hmodd : Odd ((a ^ (2 ^ E) + 1) / 2) := by
    rw [hsq]
    exact odd_div_two_sq_add_one _ hodd.pow
  have h2dvd : 2 ∣ a ^ (2 ^ E) + 1 := even_iff_two_dvd.mp hEvenn
  have hnmul : 2 * ((a ^ (2 ^ E) + 1) / 2) = a ^ (2 ^ E) + 1 := by
    rw [mul_comm]; exact Nat.div_mul_cancel h2dvd
  have h10 : 10 ≤ a ^ (2 ^ E) + 1 := by
    have h2E : 2 ≤ 2 ^ E := by
      calc (2 : ℕ) = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ E := Nat.pow_le_pow_right (by norm_num) hE
    have hle : a ^ 2 ≤ a ^ (2 ^ E) := Nat.pow_le_pow_right (by omega) h2E
    have h9 : 9 ≤ a ^ 2 := by nlinarith
    omega
  have h5 : 5 ≤ (a ^ (2 ^ E) + 1) / 2 := by
    have := Nat.div_le_div_right (c := 2) h10
    norm_num at this
    exact this
  have hmgt : 1 < (a ^ (2 ^ E) + 1) / 2 := lt_of_lt_of_le (by norm_num) h5
  obtain ⟨p, hpprime, hpdvdm⟩ := Nat.exists_prime_and_dvd (ne_of_gt hmgt)
  -- `p` is odd, divides `a ^ (2 ^ E) + 1`, and does not divide `a`
  have hp2 : p ≠ 2 := by
    intro hp
    have hEven : Even ((a ^ (2 ^ E) + 1) / 2) := even_iff_two_dvd.mpr (hp ▸ hpdvdm)
    exact (Nat.not_even_iff_odd.mpr hmodd) hEven
  have hpdvdn : p ∣ a ^ (2 ^ E) + 1 := by
    rw [← hnmul]; exact dvd_mul_of_dvd_right hpdvdm 2
  have hpa : ¬ p ∣ a := by
    intro hpa'
    have h1 : p ∣ a ^ (2 ^ E) := hpa'.trans (dvd_pow_self a (pow_ne_zero E (by norm_num)))
    have h2 := Nat.dvd_sub hpdvdn h1
    rw [Nat.add_sub_cancel_left] at h2
    exact Nat.Prime.not_dvd_one hpprime h2
  have h2p : 2 ≤ p := hpprime.two_le
  have hfactp : Fact p.Prime := ⟨hpprime⟩
  have hfact2 : Fact (2 < p) := ⟨by omega⟩
  have hza : (a : ZMod p) ≠ 0 := fun h => hpa ((ZMod.natCast_eq_zero_iff a p).mp h)
  -- `a ^ (2 ^ E) = -1` and `a ^ (2 ^ (E + 1)) = 1` in `ZMod p`, while `-1 ≠ 1`
  have hpow : (a : ZMod p) ^ (2 ^ E) = -1 := by
    have h0 : ((a ^ (2 ^ E) + 1 : ℕ) : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff _ p).mpr hpdvdn
    have h1 : (a : ZMod p) ^ (2 ^ E) + 1 = 0 := by simpa using h0
    exact eq_neg_of_add_eq_zero_left h1
  have h2E1 : (a : ZMod p) ^ (2 ^ (E + 1)) = 1 := by
    have hpow2 : 2 ^ (E + 1) = 2 ^ E * 2 := Nat.pow_succ 2 E
    rw [hpow2, pow_mul, hpow]
    ring
  -- hence the order of `a` is exactly `2 ^ (E + 1)`
  have hmain : 2 ^ E ∣ orderOf ((a : ZMod p)) := by
    have hdvd : orderOf ((a : ZMod p)) ∣ 2 ^ (E + 1) := orderOf_dvd_iff_pow_eq_one.mpr h2E1
    have hndvd : ¬ orderOf ((a : ZMod p)) ∣ 2 ^ E := by
      intro h
      have hw := orderOf_dvd_iff_pow_eq_one.mp h
      rw [hpow] at hw
      exact ZMod.neg_one_ne_one hw
    obtain ⟨k, hk_le, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
    have hk_eq : k = E + 1 := by
      by_contra hne
      have hkE : k ≤ E := by omega
      exact hndvd (by rw [hk]; exact pow_dvd_pow 2 hkE)
    rw [hk, hk_eq]
    exact pow_dvd_pow 2 (by omega)
  refine ⟨p, hpprime, hpa, hmain, ?_⟩
  -- the order divides `p - 1`, so `2 ^ E ≤ p - 1 < p`
  have hdvd : orderOf ((a : ZMod p)) ∣ p - 1 := ZMod.orderOf_dvd_card_sub_one hza
  have hdiv : 2 ^ E ∣ p - 1 := dvd_trans hmain hdvd
  have hle : 2 ^ E ≤ p - 1 := Nat.le_of_dvd (by omega) hdiv
  exact lt_of_le_of_lt hle (Nat.sub_lt hpprime.pos (by norm_num))

end NK.CFTLib.ARL
