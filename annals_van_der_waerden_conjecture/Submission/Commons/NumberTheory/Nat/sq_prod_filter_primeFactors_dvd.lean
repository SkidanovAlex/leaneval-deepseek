import Mathlib.Data.Nat.Factorization.Basic

namespace Commons.NumberTheory.Nat

/-- If every prime `p ∣ D` satisfies `p ^ 2 ∣ D` (i.e. `D` is squarefull), then for any bound
`n`, the square of the product of the prime factors of `D` exceeding `n` divides `D`. -/
theorem sq_prod_filter_primeFactors_dvd (n D : ℕ)
    (hsq : ∀ p : ℕ, Nat.Prime p → p ∣ D → p ^ 2 ∣ D) :
    (∏ p ∈ (Nat.primeFactors D).filter (fun p => n < p), p) ^ 2 ∣ D := by
  rcases eq_or_ne D 0 with rfl | hD
  · simp
  set s := (Nat.primeFactors D).filter (fun p => n < p) with hs
  have hsub : s ⊆ Nat.primeFactors D := by
    rw [hs]; exact Finset.filter_subset _ _
  rw [← Finset.prod_pow]
  conv_rhs => rw [Nat.prod_primeFactors_pow_factorization hD]
  refine (Finset.prod_dvd_prod_of_dvd (s := s) (fun p => p ^ 2)
      (fun p => p ^ D.factorization p) ?_).trans
    (Finset.prod_dvd_prod_of_subset s (Nat.primeFactors D)
      (fun p => p ^ D.factorization p) hsub)
  intro p hp
  have hp' : p ∈ Nat.primeFactors D := hsub hp
  have hpp : Nat.Prime p := Nat.prime_of_mem_primeFactors hp'
  have h2 : 2 ≤ D.factorization p :=
    (hpp.pow_dvd_iff_le_factorization hD).mp (hsq p hpp (Nat.dvd_of_mem_primeFactors hp'))
  exact pow_dvd_pow p h2

end Commons.NumberTheory.Nat