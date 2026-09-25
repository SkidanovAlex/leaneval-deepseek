import Mathlib.RingTheory.Valuation.ValuationSubring

namespace Commons.RingTheory.Valuation.ValuationSubring

theorem isUnit_iff_val_eq_one {K : Type*} [Field K] (A : ValuationSubring K) (x : A) :
    IsUnit x ↔ A.valuation (x : K) = 1 := by
  rw [ValuationSubring.valuation_eq_one_iff]

end Commons.RingTheory.Valuation.ValuationSubring