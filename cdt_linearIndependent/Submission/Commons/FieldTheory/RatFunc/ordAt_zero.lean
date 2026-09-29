import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RegularLocalRing.Defs
import Submission.Commons.FieldTheory.RatFunc.ordAt_def

namespace Commons.FieldTheory.RatFunc

/-- The zero rational function has order of vanishing `0` (the neutral convention). -/
theorem ordAt_zero {K : Type*} [Field K] (α : K) : ordAt α (0 : RatFunc K) = 0 := by
  rw [ordAt_def, RatFunc.num_zero, RatFunc.denom_zero]
  simp

end Commons.FieldTheory.RatFunc