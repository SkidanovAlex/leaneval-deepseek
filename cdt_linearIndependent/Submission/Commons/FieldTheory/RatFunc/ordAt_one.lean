import Mathlib
import Submission.Commons.FieldTheory.RatFunc.ordAt_def

namespace Commons.FieldTheory.RatFunc

/-- The constant function `1` vanishes to order `0` at every point. -/
theorem ordAt_one {K : Type*} [Field K] (α : K) : ordAt α (1 : RatFunc K) = 0 := by
  rw [ordAt_def, RatFunc.num_one, RatFunc.denom_one]
  simp

end Commons.FieldTheory.RatFunc
