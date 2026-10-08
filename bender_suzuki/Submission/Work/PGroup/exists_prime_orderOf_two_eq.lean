import Mathlib
import Submission.Work.PGroup.Cyc2Defs
import Submission.Work.PGroup.eq_orderOf_mul_prime_pow
import Submission.Work.PGroup.not_sq_dvd_PhiZ
import Submission.Work.PGroup.lt_PhiZ_of_prime_pow

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# Bang–Zsigmondy for base `2` : primes `p` with `orderOf (2 : ZMod p) = n`

For every `n ≥ 2` with `n ≠ 6` there is a prime `p` such that `2` has multiplicative order
exactly `n` modulo `p`.  Equivalently, `2 ^ n - 1` has a *primitive* prime divisor (one not
dividing any `2 ^ d - 1`, `d < n`) — Zsigmondy's theorem for `(a, b) = (2, 1)`.

The single exceptional index is `n = 6`: `Φ_6(2) = 3` and `orderOf (2 : ZMod 3) = 2`.

## Strategy

Write `Φ_n` for the `n`-th cyclotomic polynomial and `PhiZ n = Φ_n(2)` (`Cyc2Defs`).  A prime
`p ∤ n` dividing `PhiZ n` has `orderOf (2 : ZMod p) = n`
(`orderOf_two_eq_of_dvd_PhiZ`).  So it suffices to find a prime divisor of `Φ_n(2)` not dividing
`n`.  Suppose every prime divisor of `Φ_n(2)` divides `n`; then

* a prime divisor `q` of `Φ_n(2)` satisfies `n = orderOf (2 : ZMod q) · q ^ j` with `j ≥ 1`
  (`eq_orderOf_mul_prime_pow`, proved from `Φ_n(2) ∣ (2 ^ n - 1)/(2 ^ (n/ℓ) - 1)` for `ℓ ∣ n`);
* two distinct primes dividing `Φ_n(2)` cannot both divide `n` (size comparison of orders);
* hence `Φ_n(2)` has a single prime divisor `q`, appearing exactly once (`not_sq_dvd_PhiZ`);
  so `Φ_n(2) = q`;
* but `q < Φ_n(2)` (`lt_PhiZ_of_prime_pow`), the sole exception being `n = 6`.

Thus for `n ≠ 6` a prime divisor of `Φ_n(2)` outside `n` exists.
-/

namespace Work.PGroup

/-- For an odd prime `p`, the multiplicative order of `2` modulo `p` divides `p - 1`. -/
lemma orderOf_two_dvd_sub_one {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    orderOf (2 : ZMod p) ∣ p - 1 := by
  haveI : Fact p.Prime := ⟨hp⟩
  rw [orderOf_dvd_iff_pow_eq_one]
  refine ZMod.pow_card_sub_one_eq_one ?_
  intro h
  rw [show (2 : ZMod p) = ((2 : ℕ) : ZMod p) by norm_num, ZMod.natCast_eq_zero_iff] at h
  have hle : p ≤ 2 := Nat.le_of_dvd (by norm_num) h
  have h2p := hp.two_le
  omega

/-- Two distinct primes dividing both `Φ_n(2)` and `n` cannot exist. -/
lemma eq_of_prime_dvd_PhiZ_and_dvd {p q n : ℕ} (hp : p.Prime) (hq : q.Prime)
    (h2 : ¬ (2 : ℤ) ∣ PhiZ n) (hpdvd : (p : ℤ) ∣ PhiZ n) (hqdvd : (q : ℤ) ∣ PhiZ n)
    (hpn : p ∣ n) (hqn : q ∣ n) : p = q := by
  by_contra hpq
  have hp2 : p ≠ 2 := by rintro rfl; exact h2 hpdvd
  have hq2 : q ≠ 2 := by rintro rfl; exact h2 hqdvd
  obtain ⟨jp, hjp⟩ := eq_orderOf_mul_prime_pow hp hp2 hpdvd
  obtain ⟨jq, hjq⟩ := eq_orderOf_mul_prime_pow hq hq2 hqdvd
  have hqD : q ∣ orderOf (2 : ZMod p) := by
    have h : q ∣ orderOf (2 : ZMod p) * p ^ jp := by rw [← hjp]; exact hqn
    rcases (hq.dvd_mul).mp h with h | h
    · exact h
    · exact absurd ((Nat.prime_dvd_prime_iff_eq hq hp).mp (hq.dvd_of_dvd_pow h)) (Ne.symm hpq)
  have hpD : p ∣ orderOf (2 : ZMod q) := by
    have h : p ∣ orderOf (2 : ZMod q) * q ^ jq := by rw [← hjq]; exact hpn
    rcases (hp.dvd_mul).mp h with h | h
    · exact h
    · exact absurd ((Nat.prime_dvd_prime_iff_eq hp hq).mp (hp.dvd_of_dvd_pow h)) hpq
  have h1 : q ≤ p - 1 := by
    have := hp.two_le
    exact Nat.le_of_dvd (by omega) (hqD.trans (orderOf_two_dvd_sub_one hp hp2))
  have h2' : p ≤ q - 1 := by
    have := hq.two_le
    exact Nat.le_of_dvd (by omega) (hpD.trans (orderOf_two_dvd_sub_one hq hq2))
  omega

/-- For `k ≥ 2`, `k ≠ 6`, the value `Φ_k(2)` has a prime divisor which does not divide `k`.
This is the Bang–Zsigmondy statement in its cyclotomic form. -/
lemma exists_prime_dvd_PhiZ_not_dvd {k : ℕ} (hk : 2 ≤ k) (h6 : k ≠ 6) :
    ∃ p : ℕ, p.Prime ∧ (p : ℤ) ∣ PhiZ k ∧ ¬ p ∣ k := by
  classical
  by_contra hcon
  have hbad : ∀ p : ℕ, p.Prime → (p : ℤ) ∣ PhiZ k → p ∣ k := by
    intro p hp hdvd
    by_contra hpk
    exact hcon ⟨p, hp, hdvd, hpk⟩
  have hnot : ¬ (2 : ℤ) ∣ PhiZ k := not_two_dvd_PhiZ (by omega)
  obtain ⟨p, hp, hpdvd⟩ : ∃ p : ℕ, p.Prime ∧ (p : ℤ) ∣ PhiZ k := by
    have h1 : PhiN k ≠ 1 := ne_of_gt (PhiN_one_lt hk)
    obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd h1
    exact ⟨p, hp, (dvd_PhiN_iff).1 hpd⟩
  have hpk : p ∣ k := hbad p hp hpdvd
  have hp2 : p ≠ 2 := by rintro rfl; exact hnot hpdvd
  obtain ⟨j, hj⟩ := eq_orderOf_mul_prime_pow hp hp2 hpdvd
  have hj1 : 1 ≤ j := by
    by_contra h
    push_neg at h
    have hj0 : j = 0 := by omega
    rw [hj0, pow_zero, mul_one] at hj
    have hpd : p ∣ orderOf (2 : ZMod p) := by rw [← hj]; exact hpk
    have hle : p ≤ p - 1 := by
      have := hp.two_le
      exact Nat.le_of_dvd (by omega) (hpd.trans (orderOf_two_dvd_sub_one hp hp2))
    have := hp.two_le
    omega
  have huniq : ∀ q : ℕ, q.Prime → (q : ℤ) ∣ PhiZ k → q = p :=
    fun q hq hqdvd =>
      (eq_of_prime_dvd_PhiZ_and_dvd (p := p) (q := q) (n := k) hp hq hnot hpdvd hqdvd hpk
        (hbad q hq hqdvd)).symm
  have hsq : ¬ (p : ℤ) ^ 2 ∣ PhiZ k := by
    have h := not_sq_dvd_PhiZ (q := p) (D := orderOf (2 : ZMod p)) (j := j) hp hp2 rfl hj1
      (by rw [← hj]; exact hpdvd)
    rwa [← hj] at h
  have hPhi_eq : PhiZ k = (p : ℤ) := by
    have huniqN : ∀ {q : ℕ}, q.Prime → q ∣ PhiN k → q = p :=
      fun {q} hq hqd => huniq q hq ((dvd_PhiN_iff).1 hqd)
    have hm0 : PhiN k ≠ 0 := ne_of_gt (PhiN_pos k)
    have hpow : PhiN k = p ^ (PhiN k).primeFactorsList.length :=
      Nat.eq_prime_pow_of_unique_prime_dvd hm0 huniqN
    have he1 : 1 ≤ (PhiN k).primeFactorsList.length := by
      by_contra h
      push_neg at h
      have h0 : (PhiN k).primeFactorsList.length = 0 := by omega
      rw [h0, pow_zero] at hpow
      have := PhiN_one_lt hk
      omega
    have he2 : (PhiN k).primeFactorsList.length ≤ 1 := by
      by_contra h
      push_neg at h
      have hdvd : p ^ 2 ∣ PhiN k := by rw [hpow]; exact pow_dvd_pow p (by omega)
      exact hsq (by
        have h2'' : ((p ^ 2 : ℕ) : ℤ) ∣ PhiZ k := (dvd_PhiN_iff).1 hdvd
        simpa using h2'')
    have heq : PhiN k = p := by
      have hlen : (PhiN k).primeFactorsList.length = 1 := le_antisymm he2 he1
      rw [hpow, hlen, pow_one]
    rw [← PhiN_cast k, heq]
  have hne : orderOf (2 : ZMod p) * p ^ j ≠ 6 := by rw [← hj]; exact h6
  have hlt := lt_PhiZ_of_prime_pow (q := p) (D := orderOf (2 : ZMod p)) (j := j) hp hp2 rfl hj1
    hne
  rw [← hj] at hlt
  rw [hPhi_eq] at hlt
  exact absurd hlt (lt_irrefl (p : ℤ))

theorem exists_prime_orderOf_two_eq {k : ℕ} (hk : 2 ≤ k) (h6 : k ≠ 6) :
    ∃ p : ℕ, Nat.Prime p ∧ orderOf (2 : ZMod p) = k := by
  obtain ⟨p, hp, hpdvd, hpndvd⟩ := exists_prime_dvd_PhiZ_not_dvd hk h6
  exact ⟨p, hp, orderOf_two_eq_of_dvd_PhiZ p k hp hpndvd hpdvd⟩

end Work.PGroup
