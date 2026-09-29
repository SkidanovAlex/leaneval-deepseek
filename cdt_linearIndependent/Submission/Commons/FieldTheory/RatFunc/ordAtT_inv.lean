import Mathlib
import Submission.Commons.FieldTheory.RatFunc.ordAtT_def
import Submission.Commons.FieldTheory.RatFunc.ordAt_inv

namespace Commons.FieldTheory.RatFunc

open Classical
open Commons.FieldTheory.RatFunc

/-- `ordAtT` changes sign under inversion. -/
theorem ordAtT_inv {K : Type*} [Field K] (α : K) {x : RatFunc K} (hx : x ≠ 0) :
    ordAtT α x⁻¹ = -ordAtT α x := by
  rw [ordAtT_def α (inv_ne_zero hx), ordAtT_def α hx, ordAt_inv α hx]
  push_cast
  ring_nf

end Commons.FieldTheory.RatFunc
