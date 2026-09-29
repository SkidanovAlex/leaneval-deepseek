import Mathlib
import Submission.Commons.FieldTheory.RatFunc.ordAtT_def
import Submission.Commons.FieldTheory.RatFunc.ordAt_mul

namespace Commons.FieldTheory.RatFunc

open Classical
open Commons.FieldTheory.RatFunc

/-- `ordAtT` is additive on nonzero elements. -/
theorem ordAtT_mul {K : Type*} [Field K] (α : K) {x y : RatFunc K} (hx : x ≠ 0) (hy : y ≠ 0) :
    ordAtT α (x * y) = ordAtT α x + ordAtT α y := by
  have hxy : x * y ≠ 0 := mul_ne_zero hx hy
  rw [ordAtT_def α hxy, ordAtT_def α hx, ordAtT_def α hy, ordAt_mul α hx hy,
    WithTop.coe_add]

end Commons.FieldTheory.RatFunc
