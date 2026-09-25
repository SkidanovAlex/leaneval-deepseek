import Mathlib
import Submission.NK.RamificationDeep.MonoDefs
import Submission.NK.RamificationDeep.isNoetherianRing_restrictRing

namespace NK.RamificationDeep

/-- The restriction of a discrete valuation ring to a subfield is Noetherian.
This is the general form `isNoetherianRing_comap_algebraMap` proved in
`Submission.NK.RamificationDeep.isNoetherianRing_restrictRing`, restated for the
`A.comap (algebraMap K L)` notation. -/
theorem isNoetherianRing_comap {K L : Type*} [Field K] [Field L] [Algebra K L] (A : ValuationSubring L) [IsDiscreteValuationRing A] : IsNoetherianRing ↥(A.comap (algebraMap K L)) :=
  isNoetherianRing_comap_algebraMap (E := K) A

end NK.RamificationDeep
