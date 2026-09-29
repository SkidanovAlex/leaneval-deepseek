import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Submission.Commons.FieldTheory.RatFunc.ordInfT_def

namespace Commons.FieldTheory.RatFunc

/-- On a nonzero polynomial, `ordInfT` is its `natDegree`. -/
theorem ordInfT_algebraMap {K : Type*} [Field K] {p : Polynomial K} (hp : p ≠ 0) :
    ordInfT (algebraMap (Polynomial K) (RatFunc K) p)
      = ((Polynomial.natDegree p : ℤ) : WithTop ℤ) := by
  have hx : algebraMap (Polynomial K) (RatFunc K) p ≠ 0 := fun h =>
    hp (IsFractionRing.injective (Polynomial K) (RatFunc K) (by simpa using h))
  rw [ordInfT_def hx, RatFunc.num_algebraMap, RatFunc.denom_algebraMap]
  simp

end Commons.FieldTheory.RatFunc