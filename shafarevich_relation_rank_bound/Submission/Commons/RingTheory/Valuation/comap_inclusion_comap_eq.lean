import Mathlib.FieldTheory.IntermediateField.Basic
import Mathlib.RingTheory.Valuation.ValuationSubring

namespace Commons.RingTheory.Valuation

/-- Taking the `ValuationSubring` of a larger intermediate field and then restricting
along the inclusion agrees with taking it directly. -/
theorem comap_inclusion_comap_eq {K K' : Type*} [Field K] [Field K'] [Algebra K K']
    {L L₀ : IntermediateField K K'} (h : L₀ ≤ L) (A : ValuationSubring K') :
    (A.comap (algebraMap ↥L K')).comap (IntermediateField.inclusion h) =
      A.comap (algebraMap ↥L₀ K') := by
  rw [ValuationSubring.comap_comap]
  congr 1

end Commons.RingTheory.Valuation