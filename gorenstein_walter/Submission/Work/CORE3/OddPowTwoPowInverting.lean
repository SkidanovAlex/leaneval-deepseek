import Mathlib

set_option linter.style.haveILetI false

namespace Work.CORE3

/-- If `h` inverts `x`, then every odd power of `h` inverts `x` as well.

Even powers of `h` centralize `x` (`h ^ 2 * x * (h ^ 2)⁻¹ = x`, and then by induction
`(h ^ 2) ^ t` centralizes `x`), while an odd power `h ^ (2 * t + 1) = (h ^ 2) ^ t * h`
conjugates `x` to `(h ^ 2) ^ t * (h * x * h⁻¹) * ((h ^ 2) ^ t)⁻¹
= (h ^ 2) ^ t * x⁻¹ * ((h ^ 2) ^ t)⁻¹
= ((h ^ 2) ^ t * x * ((h ^ 2) ^ t)⁻¹)⁻¹ = x⁻¹`. -/
private lemma pow_odd_conj_eq_inv {G : Type*} [Group G] {h x : G}
    (hh : h * x * h⁻¹ = x⁻¹) {m : ℕ} (hm : Odd m) :
    h ^ m * x * (h ^ m)⁻¹ = x⁻¹ := by
  -- even powers of `h` centralize `x`
  have heven : ∀ t : ℕ, (h ^ 2) ^ t * x * ((h ^ 2) ^ t)⁻¹ = x := by
    have h2 : h ^ 2 * x * (h ^ 2)⁻¹ = x := by
      have e1 : h ^ 2 * x * (h ^ 2)⁻¹ = h * (h * x * h⁻¹) * h⁻¹ := by
        rw [pow_two]; group
      rw [e1, hh]
      have e2 : h * x⁻¹ * h⁻¹ = (h * x * h⁻¹)⁻¹ := by group
      rw [e2, hh, inv_inv]
    intro t
    induction t with
    | zero => simp
    | succ t ih =>
      have e : (h ^ 2) ^ (t + 1) * x * ((h ^ 2) ^ (t + 1))⁻¹
             = (h ^ 2) ^ t * (h ^ 2 * x * (h ^ 2)⁻¹) * ((h ^ 2) ^ t)⁻¹ := by
        rw [pow_succ]; group
      rw [e, h2, ih]
  obtain ⟨t, rfl⟩ := hm
  have hsplit : h ^ (2 * t + 1) = (h ^ 2) ^ t * h := by
    rw [pow_succ, pow_mul]
  rw [hsplit]
  have e : ((h ^ 2) ^ t * h) * x * ((h ^ 2) ^ t * h)⁻¹
         = (h ^ 2) ^ t * (h * x * h⁻¹) * ((h ^ 2) ^ t)⁻¹ := by group
  rw [e, hh]
  have e2 : (h ^ 2) ^ t * x⁻¹ * ((h ^ 2) ^ t)⁻¹
          = ((h ^ 2) ^ t * x * ((h ^ 2) ^ t)⁻¹)⁻¹ := by group
  rw [e2, heven t]

/-- **Gorenstein–Walter, odd-power 2-power inversion.** If `h` inverts an element `x` of odd
order `> 1`, then some *odd* power `h ^ d` of `h` inverts `x` and has order a nontrivial power
of `2`.

Write `n = orderOf h = 2 ^ a * m` with `a = padicValNat 2 n` and `m` odd.  Then `h ^ m` has
order `n / m = 2 ^ a` (`orderOf_pow`, `Nat.gcd_eq_right`) and it inverts `x` because `m` is odd
(`pow_odd_conj_eq_inv`).  Since `h ^ m` inverts `x` while `x ≠ 1` has odd order, `h ^ m ≠ 1`,
so `orderOf (h ^ m) = 2 ^ a ≠ 1`, i.e. `a ≥ 1`. -/
theorem OddPowTwoPowInverting {G : Type*} [Group G] [Finite G] {h x : G} (hx1 : x ≠ 1)
    (hxo : Odd (orderOf x)) (hhx : h * x * h⁻¹ = x⁻¹) :
    ∃ d : ℕ, Odd d ∧ h ^ d * x * (h ^ d)⁻¹ = x⁻¹ ∧ ∃ v : ℕ, 1 ≤ v ∧ orderOf (h ^ d) = 2 ^ v := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set n := orderOf h with hn
  have hn0 : n ≠ 0 := by rw [hn]; exact (orderOf_pos h).ne'
  set a := padicValNat 2 n with ha
  set m := n / 2 ^ a with hm
  -- `2 ^ a` is the exact `2`-part of `n`
  have hdvd : 2 ^ a ∣ n := by rw [ha]; exact (padicValNat_dvd_iff_le hn0).mpr le_rfl
  have hm_dvd : m ∣ n := by rw [hm]; exact Nat.div_dvd_of_dvd hdvd
  have hmeq : m * 2 ^ a = n := by rw [hm]; exact Nat.div_mul_cancel hdvd
  have hm0 : m ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at hmeq
    exact hn0 hmeq.symm
  -- `m` is odd: its `2`-adic valuation is `0`
  have hpv : padicValNat 2 m = 0 := by
    have h := padicValNat.div_pow (p := 2) (a := a) (b := n) hdvd
    rw [ha] at h
    rw [h, Nat.sub_self]
  have hm_odd : Odd m := by
    rw [← Nat.not_even_iff_odd, even_iff_two_dvd]
    intro h2
    have h3 := one_le_padicValNat_of_dvd (p := 2) hm0 h2
    omega
  -- the order of `h ^ m` is `2 ^ a`
  have hord : orderOf (h ^ m) = 2 ^ a := by
    rw [orderOf_pow, ← hn, Nat.gcd_eq_right hm_dvd, ← hmeq]
    exact Nat.mul_div_cancel_left (2 ^ a) (Nat.pos_of_ne_zero hm0)
  -- `h ^ m ≠ 1`, hence `a ≥ 1`
  have hapos : 1 ≤ a := by
    by_contra hlt
    have ha0 : a = 0 := by omega
    have hw1 : h ^ m = 1 := by
      rw [← orderOf_eq_one_iff, hord, ha0, pow_zero]
    have hconj : h ^ m * x * (h ^ m)⁻¹ = x⁻¹ := pow_odd_conj_eq_inv hhx hm_odd
    rw [hw1] at hconj
    have hxinv : x = x⁻¹ := by simpa using hconj
    have hx2 : x ^ 2 = 1 := by
      rw [pow_two]
      nth_rewrite 2 [hxinv]
      rw [mul_inv_cancel]
    have hdiv : orderOf x ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr hx2
    have ho2 : orderOf x % 2 = 1 := Nat.odd_iff.mp hxo
    have hle : orderOf x ≤ 2 := Nat.le_of_dvd (by norm_num) hdiv
    have hpos : 0 < orderOf x := orderOf_pos x
    have hone : orderOf x = 1 := by omega
    exact hx1 (orderOf_eq_one_iff.mp hone)
  exact ⟨m, hm_odd, pow_odd_conj_eq_inv hhx hm_odd, a, hapos, hord⟩

end Work.CORE3
