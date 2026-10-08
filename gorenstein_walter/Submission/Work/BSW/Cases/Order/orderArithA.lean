import Mathlib
import Submission.Work.BSW.Cases.Order.Setup

set_option linter.unusedVariables false

namespace Work.BSW.Cases.Order

/-- If `2 * m ^ 2` divides a perfect square `n ^ 2`, then `2 * m` divides `n`.
This is the "square-root" step in `orderArithA`: the number `2 * k ^ 2` is not a square but has
the same odd part as `m ^ 2`, so from `2 * k ^ 2 ∣ (d + 2) ^ 2` one recovers `2 * k ∣ d + 2`. -/
lemma two_mul_dvd_of_two_mul_sq_dvd_sq {m n : ℕ} (hm : m ≠ 0) (h : 2 * m ^ 2 ∣ n ^ 2) :
    2 * m ∣ n := by
  have hm2 : m ^ 2 ∣ n ^ 2 := dvd_trans (dvd_mul_left (m ^ 2) 2) h
  obtain ⟨s, hs⟩ := h
  have hmn : m ∣ n :=
    (UniqueFactorizationMonoid.pow_dvd_pow_iff_dvd (show (2 : ℕ) ≠ 0 by norm_num)).mp hm2
  obtain ⟨q, hq⟩ := hmn
  have hq2 : q ^ 2 = 2 * s := by
    have h' : (m * q) ^ 2 = 2 * m ^ 2 * s := by rw [← hq]; exact hs
    have h'' : m ^ 2 * q ^ 2 = m ^ 2 * (2 * s) := by
      have e : m ^ 2 * q ^ 2 = (m * q) ^ 2 := by ring
      rw [e, h']; ring
    exact Nat.mul_left_cancel (pow_pos (Nat.pos_of_ne_zero hm) 2) h''
  have h2q : 2 ∣ q := Nat.prime_two.dvd_of_dvd_pow (by rw [hq2]; exact dvd_mul_right 2 s)
  obtain ⟨t, ht⟩ := h2q
  exact ⟨t, by rw [hq, ht]; ring⟩

/-- Arithmetic core of the Gorenstein–Walter order computation.  Given the system
`r * (d + 2) ^ 2 = 2 k ^ 2 d (d + 1)` with `gcd (2 k) r = 1` (and the harmless side conditions
`k ≥ 6`, `d ≥ 2`, plus two divisibility assumptions), the only solution is `d = 2 k - 2` and
`r = (2 k - 1) (k - 1)`.

The argument: `gcd (2 k) r = 1` forces `r ∣ d (d + 1)`; substituting `d (d + 1) = r s` gives
`(d + 2) ^ 2 = 2 k ^ 2 s`, so `2 k ^ 2 ∣ (d + 2) ^ 2` and hence `2 k ∣ d + 2`, say `d + 2 = 2 k t`.
Then `s = 2 t ^ 2` and the equation collapses to `r t ^ 2 = (k t - 1) (2 k t - 1)`.  Since
`gcd (k t - 1) (k t) = 1` we get `t ^ 2 ∣ 2 k t - 1`, while `t ∣ 2 k t`; hence `t ∣ 1`, i.e.
`t = 1`, and `r = (k - 1) (2 k - 1)`. -/
theorem orderArithA (k d r : ℕ) (hk : 6 ≤ k) (hd : 2 ≤ d)
    (hcop : Nat.Coprime (2 * k) r)
    (heq : r * (d + 2) ^ 2 = 2 * k ^ 2 * d * (d + 1))
    (hdiv1 : d ∣ 2 * k * r) (hdiv2 : (d + 1) ∣ 2 * k * r) :
    r = (2 * k - 1) * (k - 1) := by
  have hkpos : 0 < k := by omega
  have hdpos : 0 < d := by omega
  have hrne : r ≠ 0 := by
    intro hr
    rw [hr, zero_mul] at heq
    have hpos : 0 < 2 * k ^ 2 * d * (d + 1) := by positivity
    omega
  have hrpos : 0 < r := Nat.pos_of_ne_zero hrne
  -- `r` is coprime to `2 * k ^ 2`
  have hcopr : Nat.Coprime r (2 * k ^ 2) := by
    have h1 : Nat.Coprime r (2 * k) := hcop.symm
    have h2 : Nat.Coprime r 2 := h1.coprime_dvd_right (dvd_mul_right 2 k)
    have h3 : Nat.Coprime r k := h1.coprime_dvd_right (dvd_mul_left k 2)
    exact h2.mul_right (h3.pow_right 2)
  -- hence `r ∣ d * (d + 1)`, say `d * (d + 1) = r * s`
  have hrd : r ∣ d * (d + 1) := by
    refine hcopr.dvd_of_dvd_mul_left ?_
    have e : 2 * k ^ 2 * (d * (d + 1)) = r * (d + 2) ^ 2 := by
      rw [heq]; ring
    rw [e]; exact dvd_mul_right r _
  obtain ⟨s, hs⟩ := hrd
  -- substituting back gives `(d + 2) ^ 2 = 2 * k ^ 2 * s`
  have hn2 : (d + 2) ^ 2 = 2 * k ^ 2 * s := by
    have h : r * (d + 2) ^ 2 = r * (2 * k ^ 2 * s) := by
      rw [heq]
      have e : 2 * k ^ 2 * d * (d + 1) = 2 * k ^ 2 * (d * (d + 1)) := by ring
      rw [e, hs]; ring
    exact Nat.mul_left_cancel hrpos h
  have h2k2dvd : 2 * k ^ 2 ∣ (d + 2) ^ 2 := ⟨s, hn2⟩
  -- so `2 * k ∣ d + 2`, say `d + 2 = 2 * k * t`
  obtain ⟨t, ht₀⟩ := two_mul_dvd_of_two_mul_sq_dvd_sq hkpos.ne' h2k2dvd
  have ht : d + 2 = 2 * (k * t) := by rw [ht₀]; ring
  set u := k * t with hu
  have htpos : 0 < t := by
    by_contra h
    have ht0 : t = 0 := by omega
    rw [ht0, mul_zero] at ht₀
    omega
  have hu1 : 1 ≤ u := by
    have : 0 < u := by rw [hu]; exact Nat.mul_pos hkpos htpos
    omega
  -- and then `s = 2 * t ^ 2`
  have hs2 : s = 2 * t ^ 2 := by
    have h : (2 * u) ^ 2 = 2 * k ^ 2 * s := by rw [← ht]; exact hn2
    have h2 : 2 * k ^ 2 * (2 * t ^ 2) = 2 * k ^ 2 * s := by
      rw [← h, hu]; ring
    exact (Nat.mul_left_cancel (Nat.mul_pos (by norm_num) (pow_pos hkpos 2)) h2).symm
  -- the equation becomes `r * t ^ 2 = (u - 1) * (2 * u - 1)`
  have hrt : r * t ^ 2 = (u - 1) * (2 * u - 1) := by
    have hL : 2 * (r * t ^ 2) = d * (d + 1) := by
      rw [hs2] at hs
      rw [hs]; ring
    have hR : 2 * ((u - 1) * (2 * u - 1)) = d * (d + 1) := by
      have hd1 : d = 2 * u - 2 := by omega
      have hd2 : d + 1 = 2 * u - 1 := by omega
      rw [hd2, hd1]
      have e : 2 * u - 2 = 2 * (u - 1) := by omega
      rw [e]; ring
    exact Nat.mul_left_cancel (by norm_num) (hL.trans hR.symm)
  -- `t ^ 2 ∣ (u - 1) * (2 * u - 1)` with `t ^ 2` coprime to `u - 1` forces `t ^ 2 ∣ 2 * u - 1`
  have ht1 : t = 1 := by
    have htdvd : t ^ 2 ∣ (u - 1) * (2 * u - 1) := ⟨r, by rw [← hrt]; ring⟩
    have hcop_ut : Nat.Coprime (u - 1) u :=
      (Nat.coprime_self_sub_left hu1).mpr (Nat.coprime_one_left u)
    have hcop_u_t : Nat.Coprime (u - 1) t :=
      hcop_ut.coprime_dvd_right (by rw [hu]; exact dvd_mul_left t k)
    have hcop2 : Nat.Coprime (t ^ 2) (u - 1) := (hcop_u_t.pow_right 2).symm
    have h1 : t ^ 2 ∣ 2 * u - 1 := hcop2.dvd_of_dvd_mul_left htdvd
    have h2 : t ∣ 2 * u - 1 := dvd_trans (show t ∣ t ^ 2 from ⟨t, by ring⟩) h1
    have h3 : t ∣ 2 * u := ⟨2 * k, by rw [hu]; ring⟩
    have h4 : t ∣ 1 := by
      have hh := Nat.dvd_sub h3 h2
      have e : 2 * u - (2 * u - 1) = 1 := by omega
      rwa [e] at hh
    exact Nat.dvd_one.mp h4
  have huk : u = k := by rw [hu, ht1, mul_one]
  rw [ht1] at hrt
  simp only [one_pow, mul_one] at hrt
  rw [huk] at hrt
  rw [hrt]
  ring

end Work.BSW.Cases.Order
