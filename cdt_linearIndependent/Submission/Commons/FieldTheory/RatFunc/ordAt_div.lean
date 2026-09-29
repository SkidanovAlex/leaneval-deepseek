import Mathlib
import Submission.Commons.FieldTheory.RatFunc.ordAt_def
import Submission.Commons.FieldTheory.RatFunc.ordAt_mul
import Submission.Commons.FieldTheory.RatFunc.ordAt_inv

namespace Commons.FieldTheory.RatFunc

/-- The order of vanishing of a quotient is the difference of the orders. -/
theorem ordAt_div {K : Type*} [Field K] (α : K) {x y : RatFunc K} (hx : x ≠ 0) (hy : y ≠ 0) :
    ordAt α (x / y) = ordAt α x - ordAt α y := by
  rw [div_eq_mul_inv, ordAt_mul α hx (inv_ne_zero hy), ordAt_inv α hy]
  ring

end Commons.FieldTheory.RatFunc
