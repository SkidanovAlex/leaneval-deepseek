import Mathlib.FieldTheory.RatFunc.Degree
import Mathlib.RingTheory.SimpleRing.Principal
import Submission.Commons.FieldTheory.RatFunc.ordInfT_def

namespace Commons.FieldTheory.RatFunc

open Classical

/-- Away from zero, `ordInfT` agrees with `RatFunc.intDegree` (as an element of `WithTop ℤ`). -/
theorem ordInfT_eq_intDegree {K : Type*} [Field K] {x : RatFunc K} (hx : x ≠ 0) :
    ordInfT x = (RatFunc.intDegree x : WithTop ℤ) := by
  rw [ordInfT_def hx, RatFunc.intDegree]
  rfl

/-- `ordInfT` is invariant under negation. -/
theorem ordInfT_neg {K : Type*} [Field K] (x : RatFunc K) : ordInfT (-x) = ordInfT x := by
  rcases eq_or_ne x 0 with rfl | hx
  · rw [neg_zero]
  · rw [ordInfT_eq_intDegree (neg_ne_zero.mpr hx), ordInfT_eq_intDegree hx, RatFunc.intDegree_neg]

end Commons.FieldTheory.RatFunc