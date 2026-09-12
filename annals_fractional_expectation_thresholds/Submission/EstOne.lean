import Mathlib.Data.Nat.Choose.Bounds
open scoped BigOperators
namespace Submission
namespace EstOne

/-- `(1 + 1/n)^n ≤ 3` for `n ≥ 1`. -/
theorem one_add_inv_pow_le_three (n : ℕ) (hn : 1 ≤ n) :
    (1 + (1 : ℝ) / n) ^ n ≤ 3 := by
  sorry
end EstOne
end Submission
