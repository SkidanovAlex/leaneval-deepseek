import Mathlib
import Submission.NK.RamificationDeep.MonoDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace NK.RamificationDeep

/-- Let `A` be a valuation subring of `L` and `B := A.comap (algebraMap K L)` its preimage in `K`.
If `A` is integral over `B`, then `A` is the integral closure of `B` in `L`.

Indeed, a valuation subring of a field is integrally closed in that field
(`ValuationSubring` supplies the instance `IsIntegrallyClosedIn ↥A L`, i.e.
`IsIntegralClosure ↥A ↥A L`), so an element `x : L` integral over `B` is integral over `A`
and hence lies in `A`; conversely every element of `A` is integral over `B` by hypothesis.
This is exactly Mathlib's `IsIntegralClosure.of_isIntegrallyClosedIn`. -/
theorem isIntegralClosure_comap {K L : Type*} [Field K] [Field L] [Algebra K L] (A : ValuationSubring L) [IsDiscreteValuationRing A] (hint : Algebra.IsIntegral ↥(A.comap (algebraMap K L)) ↥A) : IsIntegralClosure ↥A ↥(A.comap (algebraMap K L)) L :=
  IsIntegralClosure.of_isIntegrallyClosedIn

end NK.RamificationDeep
