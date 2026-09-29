import Mathlib
import Submission.Commons.FieldTheory.RatFunc.ordInfT_def
import Submission.Commons.FieldTheory.RatFunc.ordInfT_mul

namespace Commons.FieldTheory.RatFunc

/-- `ordInfT` of a quotient of nonzero elements. -/
theorem ordInfT_div {K : Type*} [Field K] {x y : RatFunc K} (hx : x ≠ 0) (hy : y ≠ 0) :
    ordInfT (x / y) = ordInfT x - ordInfT y := by
  rw [ordInfT_eq_coe_intDegree (div_ne_zero hx hy), ordInfT_eq_coe_intDegree hx,
    ordInfT_eq_coe_intDegree hy, RatFunc.intDegree_div hx hy]
  push_cast
  ring_nf

end Commons.FieldTheory.RatFunc
