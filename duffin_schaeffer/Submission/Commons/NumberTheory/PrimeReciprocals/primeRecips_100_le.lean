import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.NumberTheory.PrimeCounting

namespace Commons.NumberTheory.PrimeReciprocals

/-- The list of primes up to `100`. -/
def primesLE100 : Finset ℕ :=
  {2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47,
   53, 59, 61, 67, 71, 73, 79, 83, 89, 97}

/-- `Nat.primesLE 100` is exactly the set of the 25 primes at most `100`. -/
theorem primesLE_100_eq : Nat.primesLE 100 = primesLE100 := by decide

/-- Upper bound for the prime reciprocal sum: `Σ_{p ≤ 100} 1/p ≤ 1.803`
(true value `1.8028172...`).  Sufficient: evaluate the finite rational sum over the 25 primes
`2,3,5,...,97` (this is at most `1.80282`; either compute it exactly, or use the ceiling trick
`1/p ≤ ⌈10^5/p⌉/10^5` and evaluate the integer sum `Σ_{p≤100} ⌈10^5/p⌉ = 180291` by `decide`
together with `Nat.primesLE 100 = {2,3,5,7,11,13,17,19,23,29,31,37,41,43,47,53,59,61,67,71,73,79,83,89,97}`
(provable by `decide`)). -/
theorem primeRecips_100_le : (∑ p ∈ Nat.primesLE 100, (1 : ℝ) / (p : ℝ)) ≤ 1.803 := by
  rw [primesLE_100_eq, primesLE100]
  norm_num

end Commons.NumberTheory.PrimeReciprocals