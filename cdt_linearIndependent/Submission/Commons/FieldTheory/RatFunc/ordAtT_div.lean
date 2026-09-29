import Mathlib
import Submission.Commons.FieldTheory.RatFunc.ordAtT_def
import Submission.Commons.FieldTheory.RatFunc.ordAtT_mul
import Submission.Commons.FieldTheory.RatFunc.ordAtT_inv
import Submission.Commons.FieldTheory.RatFunc.ordAt_div

namespace Commons.FieldTheory.RatFunc

open Classical
open Commons.FieldTheory.RatFunc

/-- `ordAtT` of a quotient of nonzero rational functions. -/
theorem ordAtT_div {K : Type*} [Field K] (α : K) {x y : RatFunc K} (hx : x ≠ 0) (hy : y ≠ 0) :
    ordAtT α (x / y) = ordAtT α x - ordAtT α y := by
  have hxy : x / y ≠ 0 := div_ne_zero hx hy
  rw [ordAtT_def α hxy, ordAtT_def α hx, ordAtT_def α hy, ordAt_div α hx hy]
  push_cast
  ring_nf

end Commons.FieldTheory.RatFunc
