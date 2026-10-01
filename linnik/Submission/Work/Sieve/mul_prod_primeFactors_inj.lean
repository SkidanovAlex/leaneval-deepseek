import Mathlib

namespace Work.Sieve

/-- If `d` is squarefree, `t` and `t'` are sets of primes dividing `d`, and
`r`, `r'` are coprime to `d`, then `r * ∏_{p∈t} p = r' * ∏_{p∈t'} p` forces
`t = t'` and `r = r'`.  (The factor `∏_{p∈t} p` is the `t`-part of `d`, and the
coprimality of `r` to `d` pins down the complementary factor.) -/
lemma mul_prod_primeFactors_inj {d : ℕ} (hds : Squarefree d)
    {t t' : Finset ℕ} (ht : t ⊆ d.primeFactors) (ht' : t' ⊆ d.primeFactors)
    {r r' : ℕ} (hr : Nat.Coprime r d) (hr' : Nat.Coprime r' d)
    (h : r * (∏ p ∈ t, p) = r' * (∏ p ∈ t', p)) :
    t = t' ∧ r = r' := by
  set P := ∏ p ∈ t, p with hP
  set P' := ∏ p ∈ t', p with hP'
  -- `P` and `P'` are divisors of `d`.
  have hPdvd : P ∣ d := by
    have hs := Finset.prod_dvd_prod_of_subset t d.primeFactors (fun p => p) ht
    rwa [Nat.prod_primeFactors_of_squarefree hds] at hs
  have hP'dvd : P' ∣ d := by
    have hs := Finset.prod_dvd_prod_of_subset t' d.primeFactors (fun p => p) ht'
    rwa [Nat.prod_primeFactors_of_squarefree hds] at hs
  -- hence `P` is coprime to `r'` and `P'` is coprime to `r`.
  have hcop : Nat.Coprime P r' := (Nat.Coprime.coprime_dvd_right hPdvd hr').symm
  have hcop' : Nat.Coprime P' r := (Nat.Coprime.coprime_dvd_right hP'dvd hr).symm
  -- `P ∣ r * P = r' * P'` and `P' ∣ r' * P' = r * P`
  have hPdiv : P ∣ r' * P' := by rw [← h]; exact ⟨r, mul_comm r P⟩
  have hP'div : P' ∣ r * P := by rw [h]; exact ⟨r', mul_comm r' P'⟩
  have hPP' : P ∣ P' := hcop.dvd_of_dvd_mul_left hPdiv
  have hP'P : P' ∣ P := hcop'.dvd_of_dvd_mul_left hP'div
  have hPPeq : P = P' := Nat.dvd_antisymm hPP' hP'P
  -- the products agree, and are nonzero because each factor is a prime
  have hPpos : 0 < P := by
    rw [hP]
    exact Finset.prod_pos (fun p hp => (Nat.prime_of_mem_primeFactors (ht hp)).pos)
  have hr_eq : r = r' := by
    have h' := h
    rw [← hPPeq] at h'
    exact Nat.mul_right_cancel hPpos h'
  refine ⟨?_, hr_eq⟩
  -- equal products of pairwise coprime primes determine the set
  apply Finset.ext
  intro p
  constructor
  · intro hp
    have hpprime : p.Prime := Nat.prime_of_mem_primeFactors (ht hp)
    have hpdvd : p ∣ P' := by
      rw [← hPPeq]
      exact Finset.dvd_prod_of_mem (fun q => q) hp
    rcases (hpprime.prime.dvd_finsetProd_iff (fun q => q)).mp hpdvd with ⟨a, ha, hpa⟩
    have haprime : a.Prime := Nat.prime_of_mem_primeFactors (ht' ha)
    rcases (Nat.dvd_prime haprime).mp hpa with h1 | h1
    · exact absurd h1 hpprime.ne_one
    · rw [h1]; exact ha
  · intro hp
    have hpprime : p.Prime := Nat.prime_of_mem_primeFactors (ht' hp)
    have hpdvd : p ∣ P := by
      rw [hPPeq]
      exact Finset.dvd_prod_of_mem (fun q => q) hp
    rcases (hpprime.prime.dvd_finsetProd_iff (fun q => q)).mp hpdvd with ⟨a, ha, hpa⟩
    have haprime : a.Prime := Nat.prime_of_mem_primeFactors (ht ha)
    rcases (Nat.dvd_prime haprime).mp hpa with h1 | h1
    · exact absurd h1 hpprime.ne_one
    · rw [h1]; exact ha

end Work.Sieve
