import Mathlib.RingTheory.Valuation.ValuationSubring
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Commons.RingTheory.Valuation.ValuationSubring

theorem isUnit_iff_val_eq_one {K : Type*} [Field K] (A : ValuationSubring K) (x : A) :
    IsUnit x ↔ A.valuation (x : K) = 1 := by
  rw [ValuationSubring.valuation_eq_one_iff]

end Commons.RingTheory.Valuation.ValuationSubring