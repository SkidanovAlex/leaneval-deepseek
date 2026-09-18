import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.NumberTheory.PrimeCounting

namespace Commons.NumberTheory.Mertens

/-- The twenty-five primes up to `100`, listed explicitly. -/
theorem primesLE_100_eq :
    Nat.primesLE 100 =
      ({2,3,5,7,11,13,17,19,23,29,31,37,41,43,47,53,59,61,67,71,73,79,83,89,97} :
        Finset ℕ) := by
  decide

/-- The sum of the reciprocals of the primes up to `100` dominates `1.8028`. -/
theorem primeRecips_100_ge_18028 :
    (1.8028 : ℝ) ≤ ∑ p ∈ Nat.primesLE 100, (1 : ℝ) / (p : ℝ) := by
  rw [primesLE_100_eq]
  norm_num

end Commons.NumberTheory.Mertens