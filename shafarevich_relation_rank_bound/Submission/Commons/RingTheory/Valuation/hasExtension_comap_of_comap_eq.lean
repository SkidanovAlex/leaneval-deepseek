import Mathlib.RingTheory.Valuation.Extension

namespace Commons.RingTheory.Valuation

open _root_.Valuation

/-- The valuation subring of the contraction of a valuation along a ring homomorphism is the
contraction of the valuation subring. -/
theorem valuationSubring_comap {K L : Type*} [Field K] [Field L] [Algebra K L]
    {Γ : Type*} [LinearOrderedCommGroupWithZero Γ] (v : Valuation L Γ) :
    (v.comap (algebraMap K L)).valuationSubring = v.valuationSubring.comap (algebraMap K L) := by
  ext x
  simp [Valuation.comap_apply, Valuation.mem_valuationSubring_iff, ValuationSubring.mem_comap]

/-- If the contraction of a valuation subring `A` of `L` along `K → L` is the valuation
subring `B` of `K`, then `B.valuation` extends `A.valuation`.  Indeed, both valuations have the
same valuation subring after contraction, and a valuation is determined up to equivalence by its
valuation subring. -/
theorem hasExtension_comap_of_comap_eq {K L : Type*} [Field K] [Field L] [Algebra K L]
    (A : ValuationSubring L) (B : ValuationSubring K) (h : A.comap (algebraMap K L) = B) :
    B.valuation.HasExtension A.valuation := by
  refine ⟨?_⟩
  rw [Valuation.isEquiv_iff_valuationSubring, valuationSubring_comap]
  rw [ValuationSubring.valuationSubring_valuation, ValuationSubring.valuationSubring_valuation]
  exact h.symm

end Commons.RingTheory.Valuation