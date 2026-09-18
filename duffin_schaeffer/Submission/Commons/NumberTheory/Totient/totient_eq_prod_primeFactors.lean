import Mathlib.Data.Nat.Totient

namespace Commons.NumberTheory.Totient

open scoped BigOperators

/-- Euler's product formula for the totient function:
`φ n = ∏_{p | n} p^(a_p - 1) · (p - 1)` where `a_p = n.factorization p`
is the multiplicity of the prime `p` in `n`. -/
theorem totient_eq_prod_primeFactors (n : ℕ) (hn : n ≠ 0) :
    n.totient = ∏ p ∈ n.primeFactors, p ^ (n.factorization p - 1) * (p - 1) := by
  rw [Nat.totient_eq_prod_factorization hn]
  exact Nat.prod_factorization_eq_prod_primeFactors fun p k => p ^ (k - 1) * (p - 1)

end Commons.NumberTheory.Totient
