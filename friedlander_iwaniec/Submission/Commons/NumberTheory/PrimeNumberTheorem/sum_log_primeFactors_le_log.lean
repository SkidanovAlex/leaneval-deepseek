import Mathlib

namespace Commons.NumberTheory.PrimeNumberTheorem

/-- The sum of the logarithms of the distinct prime divisors of `q` is at most
`log q`: the radical of `q` divides `q`, and `log` is monotone. -/
theorem sum_log_primeFactors_le_log (q : ℕ) (hq : q ≠ 0) :
    (∑ p ∈ q.primeFactors, Real.log (p : ℝ)) ≤ Real.log (q : ℝ) := by
  have hne : ∀ p ∈ q.primeFactors, (p : ℝ) ≠ 0 := fun p hp =>
    (Nat.cast_ne_zero.mpr (Nat.pos_of_mem_primeFactors hp).ne')
  rw [← Real.log_prod hne]
  apply Real.log_le_log
  · exact Finset.prod_pos fun p hp => by
      exact_mod_cast (Nat.pos_of_mem_primeFactors hp : 0 < p)
  · rw [← Nat.cast_prod]
    exact_mod_cast Nat.le_of_dvd (Nat.pos_of_ne_zero hq) (Nat.prod_primeFactors_dvd q)

end Commons.NumberTheory.PrimeNumberTheorem
