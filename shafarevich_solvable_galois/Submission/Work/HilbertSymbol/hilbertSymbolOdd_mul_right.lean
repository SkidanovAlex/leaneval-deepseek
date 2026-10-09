import Mathlib
import Submission.Work.HilbertSymbol.Basic
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.HilbertSymbol

theorem hilbertSymbolOdd_mul_right (p : ℕ) [Fact p.Prime] (a b₁ b₂ : ℚˣ) :
    hilbertSymbolOdd p a (b₁ * b₂) = hilbertSymbolOdd p a b₁ * hilbertSymbolOdd p a b₂ := by
  rw [hilbertSymbolOdd, hilbertSymbolOdd, hilbertSymbolOdd, padicVal_mul p b₁ b₂,
    legendreOf_mul]
  rw [show padicVal p a * (padicVal p b₁ + padicVal p b₂) * (((p - 1) / 2 : ℕ) : ℤ)
        = padicVal p a * padicVal p b₁ * (((p - 1) / 2 : ℕ) : ℤ)
          + padicVal p a * padicVal p b₂ * (((p - 1) / 2 : ℕ) : ℤ) from by ring,
    zpow_add, mul_zpow, zpow_add]
  simp only [mul_assoc, mul_left_comm, mul_comm]

end Work.HilbertSymbol
