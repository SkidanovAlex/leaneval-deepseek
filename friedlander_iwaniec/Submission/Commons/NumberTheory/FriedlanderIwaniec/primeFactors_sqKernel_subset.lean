import Mathlib.Data.Nat.Factorization.Basic

namespace Commons.NumberTheory.FriedlanderIwaniec

theorem primeFactors_sqKernel_subset (d : ℕ) : ((Nat.primeFactors d).prod (fun p : ℕ => p ^ (d.factorization p / 2))).primeFactors ⊆ d.primeFactors := by
  rcases eq_or_ne d 0 with hd | hd
  · subst hd
    simp
  · have hdvd : (Nat.primeFactors d).prod (fun p : ℕ => p ^ (d.factorization p / 2)) ∣ d := by
      conv_rhs => rw [Nat.prod_primeFactors_pow_factorization hd]
      exact Finset.prod_dvd_prod_of_dvd (fun p : ℕ => p ^ (d.factorization p / 2))
        (fun p : ℕ => p ^ d.factorization p) (fun p _ => pow_dvd_pow p (Nat.div_le_self _ 2))
    exact Nat.primeFactors_mono hdvd hd

end Commons.NumberTheory.FriedlanderIwaniec