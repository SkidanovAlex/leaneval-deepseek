import Mathlib.RingTheory.SimpleRing.Principal
import Submission.Commons.FieldTheory.RatFunc.ordDegT_def

namespace Commons.FieldTheory.RatFunc

/-- On a nonzero polynomial, `ordDegT` is minus its `natDegree`. -/
theorem ordDegT_algebraMap {K : Type*} [Field K] {p : Polynomial K} (hp : p ≠ 0) :
    ordDegT (algebraMap (Polynomial K) (RatFunc K) p)
      = ((-(Polynomial.natDegree p) : ℤ) : WithTop ℤ) := by
  have hx : algebraMap (Polynomial K) (RatFunc K) p ≠ 0 := RatFunc.algebraMap_ne_zero hp
  rw [ordDegT_def hx, RatFunc.num_algebraMap, RatFunc.denom_algebraMap]
  simp

end Commons.FieldTheory.RatFunc