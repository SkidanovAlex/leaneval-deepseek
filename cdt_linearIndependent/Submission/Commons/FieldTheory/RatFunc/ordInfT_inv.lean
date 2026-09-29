import Mathlib
import Submission.Commons.FieldTheory.RatFunc.ordInfT_def
import Submission.Commons.FieldTheory.RatFunc.ordInfT_mul

namespace Commons.FieldTheory.RatFunc

/-- `ordInfT` of an inverse.  Away from zero `ordInfT` is `RatFunc.intDegree`, which is negated
by inversion; hence the same is true of `ordInfT`, the value at `0` being irrelevant since
`x ≠ 0` forces `x⁻¹ ≠ 0`. -/
theorem ordInfT_inv {K : Type*} [Field K] {x : RatFunc K} (hx : x ≠ 0) :
    ordInfT x⁻¹ = -ordInfT x := by
  rw [ordInfT_eq_coe_intDegree (inv_ne_zero hx), ordInfT_eq_coe_intDegree hx,
    RatFunc.intDegree_inv, WithTop.LinearOrderedAddCommGroup.coe_neg]

end Commons.FieldTheory.RatFunc
