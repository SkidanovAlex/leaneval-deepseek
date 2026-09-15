import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Order.Star.Real

namespace Commons.Analysis.Convex

/-- Power mean inequality on a finite set: for nonnegative `a i` and `n ≥ 1`,
`(∑_{i∈s} a i)^n ≤ |s|^(n-1) ∑_{i∈s} a i^n`.

This is the true version of `Commons.Analysis.Convex.sum_pow_le_card_pow_mul_sum_pow`,
whose statement is missing the necessary hypothesis `1 ≤ n` (without it, `s = ∅`, `n = 0`
gives `1 ≤ 0`).  It follows in one line from Mathlib's `pow_sum_le_card_mul_sum_pow`,
applied with `n - 1`, together with `n - 1 + 1 = n`. -/
theorem sum_pow_le_card_pow_mul_sum_pow_of_one_le {ι : Type*} (s : Finset ι) (a : ι → ℝ) (n : ℕ)
    (hn : 1 ≤ n) (ha : ∀ i ∈ s, 0 ≤ a i) :
    (∑ i ∈ s, a i) ^ n ≤ (s.card : ℝ) ^ (n - 1) * ∑ i ∈ s, a i ^ n := by
  have h := pow_sum_le_card_mul_sum_pow (s := s) (f := a) ha (n - 1)
  rw [Nat.sub_add_cancel hn] at h
  exact h

end Commons.Analysis.Convex