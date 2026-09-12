import Mathlib.Order.Interval.Finset.Nat

namespace Commons.Data.Finset

/-- Cardinality of a natural-number interval `Icc a b`. -/
theorem card_Icc_nat (a b : ℕ) : (Finset.Icc a b).card = b + 1 - a := by
  exact Nat.card_Icc a b

end Commons.Data.Finset