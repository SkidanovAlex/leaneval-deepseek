import Mathlib.Data.Nat.Factorization.Basic

namespace Commons.Data.Nat

/-- If every prime dividing `N` has its square dividing `N` (i.e. `N` is squarefull),
then the square of the radical of `N` divides `N`. -/
theorem squarefull_radical_sq_dvd (N : ℕ) (h : ∀ p : ℕ, Nat.Prime p → p ∣ N → p ^ 2 ∣ N) :
    (∏ p ∈ N.primeFactors, p) ^ 2 ∣ N := by
  rcases eq_or_ne N 0 with rfl | hN
  · simp
  rw [← Finset.prod_pow]
  conv_rhs => rw [Nat.prod_primeFactors_pow_factorization hN]
  refine Finset.prod_dvd_prod_of_dvd (fun p => p ^ 2) (fun p => p ^ N.factorization p) ?_
  intro p hp
  have hpp : Nat.Prime p := Nat.prime_of_mem_primeFactors hp
  have h2 : 2 ≤ N.factorization p :=
    (hpp.pow_dvd_iff_le_factorization hN).mp (h p hpp (Nat.dvd_of_mem_primeFactors hp))
  exact pow_dvd_pow p h2

end Commons.Data.Nat