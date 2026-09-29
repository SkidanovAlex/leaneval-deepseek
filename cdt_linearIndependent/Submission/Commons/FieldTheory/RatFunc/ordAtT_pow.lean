import Mathlib
import Submission.Commons.FieldTheory.RatFunc.ordAtT_def
import Submission.Commons.FieldTheory.RatFunc.ordAt_pow

namespace Commons.FieldTheory.RatFunc

open Classical
open Commons.FieldTheory.RatFunc

/-- `ordAtT` of a power of a nonzero rational function. -/
theorem ordAtT_pow {K : Type*} [Field K] (α : K) {x : RatFunc K} (hx : x ≠ 0) (n : ℕ) :
    ordAtT α (x ^ n) = (n : ℤ) * ordAtT α x := by
  have hxn : x ^ n ≠ 0 := pow_ne_zero n hx
  rw [ordAtT_def α hxn, ordAtT_def α hx, ordAt_pow α x n, WithTop.coe_mul]

end Commons.FieldTheory.RatFunc
