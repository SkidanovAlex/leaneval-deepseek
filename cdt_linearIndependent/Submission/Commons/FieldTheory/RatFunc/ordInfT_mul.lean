import Mathlib.FieldTheory.RatFunc.Degree
import Mathlib.RingTheory.SimpleRing.Principal
import Submission.Commons.FieldTheory.RatFunc.ordInfT_def

namespace Commons.FieldTheory.RatFunc

/-- On a nonzero rational function, `ordInfT` is Mathlib's `RatFunc.intDegree`
(read in `WithTop ℤ` through the coercion). -/
theorem ordInfT_eq_coe_intDegree {K : Type*} [Field K] {x : RatFunc K} (hx : x ≠ 0) :
    ordInfT x = (RatFunc.intDegree x : WithTop ℤ) := by
  rw [ordInfT_def hx, RatFunc.intDegree, WithTop.LinearOrderedAddCommGroup.coe_sub]

/-- `ordInfT` is additive on nonzero elements. -/
theorem ordInfT_mul {K : Type*} [Field K] {x y : RatFunc K} (hx : x ≠ 0) (hy : y ≠ 0) :
    ordInfT (x * y) = ordInfT x + ordInfT y := by
  rw [ordInfT_eq_coe_intDegree (mul_ne_zero hx hy), ordInfT_eq_coe_intDegree hx,
    ordInfT_eq_coe_intDegree hy, RatFunc.intDegree_mul hx hy, WithTop.coe_add]

end Commons.FieldTheory.RatFunc