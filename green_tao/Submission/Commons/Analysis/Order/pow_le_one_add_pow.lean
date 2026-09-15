import Mathlib

namespace Commons.Analysis.Order

open Finset
open scoped BigOperators

/-- The elementary inequality `x ^ n ≤ 1 + x ^ m` for `0 ≤ x` and `n ≤ m`. -/
theorem pow_le_one_add_pow {x : ℝ} (hx : 0 ≤ x) {n m : ℕ} (hnm : n ≤ m) : x ^ n ≤ 1 + x ^ m := by
  rcases lt_or_ge x 1 with hx1 | hx1
  · calc x ^ n ≤ 1 := pow_le_one₀ hx hx1.le
      _ ≤ 1 + x ^ m := le_add_of_nonneg_right (pow_nonneg hx m)
  · have hle : x ^ n ≤ x ^ m := pow_le_pow_right₀ hx1 hnm
    have hpos : (0:ℝ) ≤ x ^ m := pow_nonneg hx m
    linarith

end Commons.Analysis.Order
