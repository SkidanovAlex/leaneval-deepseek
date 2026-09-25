import Mathlib
import Submission.Commons.NumberTheory.Chebyshev.theta_lower_ninetenths
import Submission.Commons.NumberTheory.Chebyshev.theta_upper_11056
import Submission.Commons.NumberTheory.Goldbach.prime_in_short_interval

namespace Commons.NumberTheory.Primes

/-- For every real `x ≥ 1530` the interval `(x, (123/100) x]` contains a prime.

This follows from the explicit Chebyshev bounds `(9/10) x ≤ θ x` and
`θ x ≤ (11056/10000) x` valid for `x ≥ 1530`, together with the fact that a
strict increase of `θ` over an interval forces a prime inside it:
since `(9/10)·(123/100) = 1107/1000 > 11056/10000`, we get
`θ x ≤ (11056/10000) x < (1107/1000) x ≤ θ ((123/100) x)`, hence
`θ x < θ ((123/100) x)`. -/
theorem prime_gap_123 (x : ℝ) (hx : 1530 ≤ x) :
    ∃ p : ℕ, Nat.Prime p ∧ x < (p : ℝ) ∧ (p : ℝ) ≤ (123 / 100) * x := by
  have hx' : 1530 ≤ (123 / 100 : ℝ) * x := by nlinarith [hx]
  have hlow :=
    Commons.NumberTheory.Chebyshev.theta_lower_ninetenths ((123 / 100 : ℝ) * x) hx'
  have hup := Commons.NumberTheory.Chebyshev.theta_upper_11056 x hx
  have hlt : Chebyshev.theta x < Chebyshev.theta ((123 / 100 : ℝ) * x) := by
    nlinarith [hlow, hup, hx]
  exact Commons.NumberTheory.Goldbach.exists_prime_of_theta_lt hlt

end Commons.NumberTheory.Primes
