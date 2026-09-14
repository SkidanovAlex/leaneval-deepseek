import Submission.Commons.GroupTheory.PGroup.exists_mul_mem_iInter_of_isPGroup_quotient

namespace Commons.NumberTheory.Nat

theorem pow_prod_filter_factorization_dvd (n D j : ℕ) :
    (∏ p ∈ (Nat.primeFactors D).filter (fun p => n < p ∧ j ≤ D.factorization p), p) ^ j ∣ D := by
  rw [← Finset.prod_pow]
  refine Commons.GroupTheory.PGroup.finset_prod_dvd_of_pairwise_coprime
    (a := fun p => p ^ j)
    ((Nat.primeFactors D).filter (fun p => n < p ∧ j ≤ D.factorization p)) ?_ ?_
  · intro i hi k hk hik
    obtain ⟨hiF, _⟩ := Finset.mem_filter.mp hi
    obtain ⟨hkF, _⟩ := Finset.mem_filter.mp hk
    have hip : Nat.Prime i := (Nat.mem_primeFactors.mp hiF).1
    have hkp : Nat.Prime k := (Nat.mem_primeFactors.mp hkF).1
    exact Nat.Coprime.pow j j ((Nat.coprime_primes hip hkp).mpr hik)
  · intro p hp
    obtain ⟨hpF, hpcond⟩ := Finset.mem_filter.mp hp
    obtain ⟨hpp, -, hD0⟩ := Nat.mem_primeFactors.mp hpF
    exact (hpp.pow_dvd_iff_le_factorization hD0).mpr hpcond.2

end Commons.NumberTheory.Nat
