import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RegularLocalRing.Defs
import Submission.Commons.Algebra.Polynomial.dnum_def

namespace Commons.Algebra.Polynomial

open Classical
open Commons.Algebra.Polynomial

/-- The falling factorial `(N)_j` is nonzero in any characteristic-zero field as soon as none of
the factors `N − k` (`k < j`) vanishes. -/
theorem fallFact_cast_ne_zero {K : Type*} [Field K] [CharZero K] {N : ℤ} {j : ℕ}
    (h : ∀ k : ℕ, k < j → N - (k : ℤ) ≠ 0) : ((fallFact N j : ℤ) : K) ≠ 0 := by
  rw [fallFact, Int.cast_prod]
  exact Finset.prod_ne_zero_iff.mpr fun k hk => by
    rw [Int.cast_ne_zero]
    exact h k (Finset.mem_range.mp hk)

end Commons.Algebra.Polynomial