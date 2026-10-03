import Mathlib
import Submission.Commons.NumberTheory.PrimeNumberTheorem.sum_log_primeFactors_le_log

namespace Commons.NumberTheory.Nat

/-- The sum of the logarithms of the distinct prime divisors of `n` is at most
`log n`.  For `n ≠ 0` this is the radical-divides-`n` argument; for `n = 0` both
sides are `0`. -/
theorem sum_log_primeFactors_le_log (n : ℕ) :
    ∑ p ∈ n.primeFactors, Real.log (p : ℝ) ≤ Real.log (n : ℝ) := by
  rcases eq_or_ne n 0 with hn | hn
  · subst hn
    simp
  · exact Commons.NumberTheory.PrimeNumberTheorem.sum_log_primeFactors_le_log n hn

end Commons.NumberTheory.Nat
