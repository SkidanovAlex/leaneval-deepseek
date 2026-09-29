import Mathlib
import Submission.Commons.FieldTheory.RatFunc.ordDegT_def
import Submission.Commons.FieldTheory.RatFunc.ordInfT_div

namespace Commons.FieldTheory.RatFunc

/-- `ordDegT` is the negative of `ordInfT` away from zero: the degree valuation at infinity is
`-ordInfT`, exactly as `ordDegT_def` records it in terms of `natDegree`.  Only the value at `0`
differs (`⊤` for both), and it is irrelevant here since the hypothesis is `x ≠ 0`. -/
theorem ordDegT_eq_neg_ordInfT {K : Type*} [Field K] {x : RatFunc K} (hx : x ≠ 0) :
    ordDegT x = -ordInfT x := by
  rw [ordDegT_def hx, ordInfT_def hx]
  simp only [← WithTop.LinearOrderedAddCommGroup.coe_sub,
    ← WithTop.LinearOrderedAddCommGroup.coe_neg]
  congr 1
  ring

/-- `ordDegT` of a quotient of nonzero elements. -/
theorem ordDegT_div {K : Type*} [Field K] {x y : RatFunc K} (hx : x ≠ 0) (hy : y ≠ 0) :
    ordDegT (x / y) = ordDegT x - ordDegT y := by
  have hxy : x / y ≠ 0 := div_ne_zero hx hy
  have h1 : ordInfT (x / y) = (RatFunc.intDegree (x / y) : WithTop ℤ) :=
    ordInfT_eq_coe_intDegree hxy
  have h2 : ordInfT x = (RatFunc.intDegree x : WithTop ℤ) := ordInfT_eq_coe_intDegree hx
  have h3 : ordInfT y = (RatFunc.intDegree y : WithTop ℤ) := ordInfT_eq_coe_intDegree hy
  rw [ordDegT_eq_neg_ordInfT hxy, ordDegT_eq_neg_ordInfT hx, ordDegT_eq_neg_ordInfT hy,
    h1, h2, h3]
  simp only [← WithTop.LinearOrderedAddCommGroup.coe_sub,
    ← WithTop.LinearOrderedAddCommGroup.coe_neg]
  congr 1
  rw [RatFunc.intDegree_div hx hy]
  ring

end Commons.FieldTheory.RatFunc
