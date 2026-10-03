import Mathlib

namespace Work.ORLyndon

/-- Multiplying an integer by its sign (`1` when nonnegative, `-1` when negative) returns its
absolute value, coerced back to `ℤ`. -/
theorem mul_ite_one_neg_one_eq_natAbs (d : ℤ) :
    d * (if 0 ≤ d then (1 : ℤ) else -1) = ((d.natAbs : ℕ) : ℤ) := by
  by_cases h : 0 ≤ d
  · rw [if_pos h, mul_one, Int.natAbs_of_nonneg h]
  · rw [if_neg h, mul_neg_one, ← Int.natAbs_neg,
      Int.natAbs_of_nonneg (by omega : (0 : ℤ) ≤ -d)]

end Work.ORLyndon
