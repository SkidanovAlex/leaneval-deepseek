import Mathlib
import Submission.Work.HilbertSymbol.Basic
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.HilbertSymbol

theorem hilbertSymbolOdd_mul_left (p : ℕ) [Fact p.Prime] (a₁ a₂ b : ℚˣ) :
    hilbertSymbolOdd p (a₁ * a₂) b = hilbertSymbolOdd p a₁ b * hilbertSymbolOdd p a₂ b := by
  rw [hilbertSymbolOdd, hilbertSymbolOdd, hilbertSymbolOdd, padicVal_mul p a₁ a₂,
    legendreOf_mul]
  rw [show (padicVal p a₁ + padicVal p a₂) * padicVal p b * (((p - 1) / 2 : ℕ) : ℤ)
        = padicVal p a₁ * padicVal p b * (((p - 1) / 2 : ℕ) : ℤ)
          + padicVal p a₂ * padicVal p b * (((p - 1) / 2 : ℕ) : ℤ) from by ring,
    zpow_add, mul_zpow, zpow_add]
  simp only [mul_assoc, mul_left_comm, mul_comm]

end Work.HilbertSymbol
