import Mathlib
import Submission.Work.HilbertSymbol.Basic
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.HilbertSymbol

/-- Every unit of `ℤ` (= `{±1}`) has order dividing two. -/
private theorem intUnits_sq (u : ℤˣ) : u ^ 2 = 1 := by
  rcases Int.units_eq_one_or u with h | h <;> rw [h] <;> decide

/-- Every unit of `ℤ` has order dividing two, for integer exponents. -/
private theorem intUnits_zpow_two (u : ℤˣ) : u ^ (2 : ℤ) = 1 := by
  rcases Int.units_eq_one_or u with h | h <;> rw [h] <;> decide

/-- A unit of `ℤ` raised to an even integer power is trivial. -/
private theorem intUnits_zpow_even (u : ℤˣ) (n : ℤ) : u ^ (2 * n) = 1 := by
  rw [zpow_mul, intUnits_zpow_two, one_zpow]

theorem hilbertSymbolOdd_sq_right (p : ℕ) [Fact p.Prime] (a b : ℚˣ) :
    hilbertSymbolOdd p a (b ^ 2) = 1 := by
  have hval : padicVal p (b ^ 2) = 2 * padicVal p b := by
    rw [sq, padicVal_mul p b b]
    ring
  have hleg : legendreOf p (b ^ 2) = 1 := by
    rw [sq, legendreOf_mul, ← sq, intUnits_sq]
  rw [hilbertSymbolOdd, hval, hleg]
  rw [show padicVal p a * (2 * padicVal p b) * (((p - 1) / 2 : ℕ) : ℤ)
        = 2 * (padicVal p a * padicVal p b * (((p - 1) / 2 : ℕ) : ℤ)) from by ring,
    intUnits_zpow_even, intUnits_zpow_even, one_zpow]
  simp

end Work.HilbertSymbol
