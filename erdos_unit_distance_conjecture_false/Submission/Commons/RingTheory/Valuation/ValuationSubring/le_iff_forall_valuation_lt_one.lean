import Mathlib.RingTheory.Valuation.ValuationSubring

namespace Commons.RingTheory.Valuation.ValuationSubring

theorem le_iff_forall_valuation_lt_one {K : Type*} [Field K] (A B : ValuationSubring K) :
    A ≤ B ↔ ∀ x : K, B.valuation x < 1 → A.valuation x < 1 := by
  rw [← ValuationSubring.nonunits_le_nonunits]
  rfl

end Commons.RingTheory.Valuation.ValuationSubring