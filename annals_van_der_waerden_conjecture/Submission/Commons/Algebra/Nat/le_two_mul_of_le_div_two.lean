import Mathlib

namespace Commons.Algebra.Nat

theorem le_two_mul_of_le_div_two (n a : ℕ) (ha : a ≤ (n + 2) / 2) : 2 * a ≤ n + 2 := by
  omega

end Commons.Algebra.Nat
