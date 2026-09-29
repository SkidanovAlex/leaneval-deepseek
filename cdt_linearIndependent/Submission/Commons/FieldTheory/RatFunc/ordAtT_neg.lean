import Mathlib
import Submission.Commons.FieldTheory.RatFunc.ordAtT_def
import Submission.Commons.FieldTheory.RatFunc.ordAt_neg

namespace Commons.FieldTheory.RatFunc

open Classical
open Commons.FieldTheory.RatFunc

/-- `ordAtT` is invariant under negation. -/
theorem ordAtT_neg {K : Type*} [Field K] (α : K) (x : RatFunc K) :
    ordAtT α (-x) = ordAtT α x := by
  rcases eq_or_ne x 0 with rfl | hx
  · rw [neg_zero]
  · have hnx : -x ≠ 0 := neg_ne_zero.mpr hx
    rw [ordAtT_def α (x := -x) hnx, ordAtT_def α (x := x) hx, ordAt_neg]

end Commons.FieldTheory.RatFunc
