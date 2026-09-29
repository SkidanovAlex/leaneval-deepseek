import Mathlib
import Submission.Commons.FieldTheory.RatFunc.ordAtT_def
import Submission.Commons.FieldTheory.RatFunc.ordAt_algebraMap

namespace Commons.FieldTheory.RatFunc

open Classical
open Commons.FieldTheory.RatFunc

/-- On a nonzero polynomial, `ordAtT` is the root multiplicity. -/
theorem ordAtT_algebraMap {K : Type*} [Field K] {α : K} {p : Polynomial K} (hp : p ≠ 0) :
    ordAtT α (algebraMap (Polynomial K) (RatFunc K) p)
      = ((Polynomial.rootMultiplicity α p : ℤ) : WithTop ℤ) := by
  have hx : algebraMap (Polynomial K) (RatFunc K) p ≠ 0 := fun h =>
    hp (IsFractionRing.injective (Polynomial K) (RatFunc K) (by simpa using h))
  rw [ordAtT_def α hx, ordAt_algebraMap α p]

end Commons.FieldTheory.RatFunc
