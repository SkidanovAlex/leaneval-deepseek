import Mathlib
import Submission.Work.HilbertSymbol.Basic
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.HilbertSymbol

/-- The `p`-adic valuation of the prime `p`, viewed as an element of `ℚˣ`, equals `1`. -/
theorem padicVal_primeUnit (p : ℕ) [Fact p.Prime] : padicVal p (primeUnit p) = 1 := by
  simp [padicVal, primeUnit, ratUnit, padicValRat.self (Fact.out : p.Prime).one_lt]

/-- The `p`-adic unit part of the prime `p` is `1`. -/
theorem unitPart_primeUnit (p : ℕ) [Fact p.Prime] : unitPart p (primeUnit p) = 1 := by
  have hval : unitVal p (primeUnit p) = 1 := by
    rw [unitVal, padicVal_primeUnit, primeUnit, ratUnit, zpow_neg_one]
    simp
  apply Units.ext
  apply PadicInt.ext
  rw [unitPart_coe, Units.val_one]
  exact hval

/-- The Legendre symbol of the prime `p` (as a character of `ℚˣ`) is `1`. -/
theorem legendreOf_primeUnit (p : ℕ) [Fact p.Prime] : legendreOf p (primeUnit p) = 1 := by
  rw [legendreOf, unitPart_primeUnit, legendreUnit_one]

theorem hilbertSymbolOdd_primeUnit_self (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) :
    hilbertSymbolOdd p (primeUnit p) (primeUnit p)
      = (-1 : ℤˣ) ^ (((p - 1) / 2 : ℕ) : ℤ) := by
  have _ := hp
  rw [hilbertSymbolOdd, padicVal_primeUnit, legendreOf_primeUnit]
  simp

end Work.HilbertSymbol
