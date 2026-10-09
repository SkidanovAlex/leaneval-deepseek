/-
The Hilbert symbol at a finite odd place of `ℚ` is a bilinear pairing with values in
`ℤˣ = {±1}`, a group of exponent two: `(a, b)_p · (a, b)_p = 1`.  Hence

  `(a², b)_p = (a, b)_p · (a, b)_p = 1`.

This file deduces that consequence directly from the explicit formula which defines
`hilbertSymbolOdd`: the valuation `v_p(a²) = 2 v_p(a)` is even, the Legendre symbol
`(u(a²)/p) = (u(a)/p)² = 1` is a square in `{±1}`, and every remaining exponent of
`±1` that occurs is even.
-/
import Mathlib
import Submission.Work.HilbertSymbol.Basic
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.HilbertSymbol

/-- The group `ℤˣ = {±1}` has exponent two: the square of every unit of `ℤ` is `1`. -/
theorem intUnit_mul_self (u : ℤˣ) : u * u = 1 := by
  rcases Int.units_eq_one_or u with h | h <;> rw [h] <;> decide

/-- Every even power of a unit of `ℤ` equals `1`. -/
theorem intUnit_zpow_even (u : ℤˣ) (n : ℤ) : u ^ (2 * n) = 1 := by
  rw [show (2 : ℤ) * n = n * 2 by ring, zpow_mul, zpow_two, intUnit_mul_self]

/-- `(a², b)_p = 1` for every odd prime `p` and all `a b : ℚˣ`. -/
theorem hilbertSymbolOdd_sq_left (p : ℕ) [Fact p.Prime] (a b : ℚˣ) :
    hilbertSymbolOdd p (a ^ 2) b = 1 := by
  have hval : padicVal p (a ^ 2) = 2 * padicVal p a := by
    rw [pow_two, padicVal_mul p a a]; ring
  have hleg : legendreOf p (a ^ 2) = 1 := by
    rw [pow_two, legendreOf_mul]; exact intUnit_mul_self _
  rw [hilbertSymbolOdd, hval, hleg]
  rw [show 2 * padicVal p a * padicVal p b * (((p - 1) / 2 : ℕ) : ℤ)
       = 2 * (padicVal p a * padicVal p b * (((p - 1) / 2 : ℕ) : ℤ)) by ring]
  simp only [intUnit_zpow_even, one_zpow, mul_one]

end Work.HilbertSymbol
