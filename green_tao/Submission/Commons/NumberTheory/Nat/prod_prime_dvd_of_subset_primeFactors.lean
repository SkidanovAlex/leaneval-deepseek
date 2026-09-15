import Mathlib.Data.Nat.Factorization.Basic

namespace Commons.NumberTheory.Nat

theorem prod_prime_dvd_of_subset_primeFactors {t : Finset ℕ} {n : ℕ}
    (ht : ∀ p ∈ t, Nat.Prime p) (h : t ⊆ n.primeFactors) : (∏ p ∈ t, p) ∣ n :=
  dvd_trans (Finset.prod_dvd_prod_of_subset t n.primeFactors (fun p => p) h)
    (Nat.prod_primeFactors_dvd n)

end Commons.NumberTheory.Nat