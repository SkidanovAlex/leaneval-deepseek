import Mathlib
import Submission.Commons.FieldTheory.RatFunc.ordAt_def

namespace Commons.FieldTheory.RatFunc

open Classical
open Commons.FieldTheory.RatFunc

/-- The order of vanishing with value `⊤` at zero: `ordAtT α x = ordAt α x` for `x ≠ 0` and
`ordAtT α 0 = ⊤`.  This is the valuation for which the `min` rule and the strict-dominance rule
hold with no side conditions, as needed by the Frobenius/indicial analysis of a linear
differential operator. -/
noncomputable def ordAtT {K : Type*} [Field K] (α : K) (x : RatFunc K) : WithTop ℤ :=
  if x = 0 then ⊤ else ↑(ordAt α x)

/-- Unfolding formula for `ordAtT` away from zero. -/
theorem ordAtT_def {K : Type*} [Field K] (α : K) {x : RatFunc K} (hx : x ≠ 0) :
    ordAtT α x = (ordAt α x : WithTop ℤ) := by
  rw [ordAtT, if_neg hx]

end Commons.FieldTheory.RatFunc
