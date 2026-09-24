import Mathlib
import Submission.Work.NumberTheory.Chen.BTermCount.BLodDefs

namespace Work.NumberTheory.Chen.BTermCount

noncomputable def tSmall (Y t : ℕ) : ℕ :=
  ∏ p ∈ t.primeFactors.filter (fun p => p < Y), p ^ (t.factorization p)
noncomputable def tLarge (Y t : ℕ) : ℕ :=
  ∏ p ∈ t.primeFactors.filter (fun p => Y ≤ p), p ^ (t.factorization p)

/-! ## Splitting `t` into its primes below and above `Y`

`tSmall Y t` collects the prime power factors of `t` at primes `p < Y` and
`tLarge Y t` those at primes `Y ≤ p`; the two are coprime and their product is
`t`.  The two auxiliary lemmas describe the prime divisors: every prime dividing
`tSmall Y t` is `< Y`, and every prime dividing `tLarge Y t` is `≥ Y`. -/

theorem tSmall_mul_tLarge (Y t : ℕ) (ht : t ≠ 0) : tSmall Y t * tLarge Y t = t := by
  rw [tSmall, tLarge]
  have hfilter : t.primeFactors.filter (fun p => Y ≤ p)
      = t.primeFactors.filter (fun p => ¬ p < Y) := by
    apply Finset.filter_congr
    intro p _
    exact ⟨fun h => not_lt.mpr h, fun h => not_lt.mp h⟩
  rw [hfilter]
  rw [Finset.prod_filter_mul_prod_filter_not (s := t.primeFactors)
        (p := fun p => p < Y) (f := fun p => p ^ t.factorization p)]
  exact (Nat.prod_primeFactors_pow_factorization ht).symm

theorem prime_dvd_tSmall_lt {Y t p : ℕ} (hp : p.Prime) (h : p ∣ tSmall Y t) : p < Y := by
  rw [tSmall] at h
  obtain ⟨r, hr, hpr⟩ := (Prime.dvd_finsetProd_iff (Nat.prime_iff.mp hp) _).mp h
  rw [Finset.mem_filter] at hr
  have hrp : r.Prime := Nat.prime_of_mem_primeFactors hr.1
  have hpr' : p ∣ r := hp.dvd_of_dvd_pow hpr
  have heq : p = r := (Nat.prime_dvd_prime_iff_eq hp hrp).mp hpr'
  omega

theorem prime_dvd_tLarge_ge {Y t p : ℕ} (hp : p.Prime) (h : p ∣ tLarge Y t) : Y ≤ p := by
  rw [tLarge] at h
  obtain ⟨r, hr, hpr⟩ := (Prime.dvd_finsetProd_iff (Nat.prime_iff.mp hp) _).mp h
  rw [Finset.mem_filter] at hr
  have hrp : r.Prime := Nat.prime_of_mem_primeFactors hr.1
  have hpr' : p ∣ r := hp.dvd_of_dvd_pow hpr
  have heq : p = r := (Nat.prime_dvd_prime_iff_eq hp hrp).mp hpr'
  omega

theorem BLodSmallLargeSplit (Y t : ℕ) (ht : t ≠ 0) {q m : ℕ} (hq : q.Prime) (hqY : q < Y)
    (hm : ∀ p : ℕ, p.Prime → p ∣ m → Y ≤ p) :
    (t ∣ q * m) ↔ (tSmall Y t ∣ q ∧ tLarge Y t ∣ m) := by
  have hsplit := tSmall_mul_tLarge Y t ht
  have htS : tSmall Y t ∣ t := ⟨tLarge Y t, hsplit.symm⟩
  have htL : tLarge Y t ∣ t := ⟨tSmall Y t, by rw [mul_comm]; exact hsplit.symm⟩
  constructor
  · intro h
    have h1 : tSmall Y t ∣ q * m := htS.trans h
    have h2 : tLarge Y t ∣ q * m := htL.trans h
    -- `tSmall Y t` is coprime to `m`: its primes are `< Y`, those of `m` are `≥ Y`
    have hcopS : Nat.Coprime (tSmall Y t) m := by
      by_contra hcon
      rw [Nat.Prime.not_coprime_iff_dvd] at hcon
      obtain ⟨p, hp, hpt, hpm⟩ := hcon
      have hpY : p < Y := prime_dvd_tSmall_lt hp hpt
      have hYp : Y ≤ p := hm p hp hpm
      omega
    -- `tLarge Y t` is coprime to the prime `q`: its primes are `≥ Y > q`
    have hcopL : Nat.Coprime (tLarge Y t) q := by
      by_contra hcon
      rw [Nat.Prime.not_coprime_iff_dvd] at hcon
      obtain ⟨p, hp, hpt, hpq⟩ := hcon
      have hYp : Y ≤ p := prime_dvd_tLarge_ge hp hpt
      have heq : p = q := (Nat.prime_dvd_prime_iff_eq hp hq).mp hpq
      omega
    refine ⟨?_, ?_⟩
    · exact hcopS.dvd_of_dvd_mul_right h1
    · exact hcopL.dvd_of_dvd_mul_left h2
  · rintro ⟨h1, h2⟩
    rw [← hsplit]
    exact mul_dvd_mul h1 h2

end Work.NumberTheory.Chen.BTermCount
