import Mathlib

/-!
# A two-term Taylor lower bound for `cosh`

For every real `x`, `1 + x ^ 2 / 2 ≤ Real.cosh x`.

This is the two-term truncation of the absolutely convergent series
`cosh x = ∑' n, x ^ (2n) / (2n)!`, whose terms are all nonnegative.
-/

namespace Work.Mostow

open scoped Nat

theorem diniCoshBound (x : ℝ) : 1 + x ^ 2 / 2 ≤ Real.cosh x := by
  have hsum : Summable (fun n : ℕ => x ^ (2 * n) / (↑(2 * n)! : ℝ)) :=
    (Real.hasSum_cosh x).summable
  have h := hsum.sum_le_tsum ({0, 1} : Finset ℕ) (fun n _ => by
    apply div_nonneg
    · rw [pow_mul]; positivity
    · positivity)
  rw [← Real.cosh_eq_tsum x] at h
  simpa using h

end Work.Mostow
