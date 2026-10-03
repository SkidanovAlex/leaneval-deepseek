import Mathlib

namespace Work.FIArea7.smallCInner2EpsAux

theorem cardDivisorsMulLe (m n : ℕ) : (m * n).divisors.card ≤ m.divisors.card * n.divisors.card := by
  rw [Nat.divisors_mul]
  exact Finset.card_mul_le

end Work.FIArea7.smallCInner2EpsAux
