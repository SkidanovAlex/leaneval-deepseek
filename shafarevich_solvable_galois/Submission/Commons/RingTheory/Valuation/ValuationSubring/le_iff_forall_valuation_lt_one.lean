import Mathlib.RingTheory.Valuation.ValuationSubring
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Commons.RingTheory.Valuation.ValuationSubring

theorem le_iff_forall_valuation_lt_one {K : Type*} [Field K] (A B : ValuationSubring K) :
    A ≤ B ↔ ∀ x : K, B.valuation x < 1 → A.valuation x < 1 := by
  rw [← ValuationSubring.nonunits_le_nonunits]
  rfl

end Commons.RingTheory.Valuation.ValuationSubring