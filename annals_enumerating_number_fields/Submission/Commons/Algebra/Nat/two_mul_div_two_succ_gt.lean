import Mathlib

namespace Commons.Algebra.Nat

/-- For every natural `n`, `n` is strictly less than twice the floor of `(n+2)/2`.
Equivalently: rounding `(n+2)` down to an even number yields something `> n`. -/
theorem two_mul_div_two_succ_gt (n : ℕ) : n < 2 * ((n + 2) / 2) := by
  rcases Nat.mod_two_eq_zero_or_one (n + 2) with h | h
  · -- `n + 2` is even: `2 * ((n+2)/2) = n + 2`
    have hmod := Nat.mod_add_div (n + 2) 2
    omega
  · -- `n + 2` is odd: `2 * ((n+2)/2) = n + 1`
    have hmod := Nat.mod_add_div (n + 2) 2
    omega

end Commons.Algebra.Nat
