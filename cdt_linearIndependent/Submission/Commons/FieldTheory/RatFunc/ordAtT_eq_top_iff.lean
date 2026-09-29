import Mathlib
import Submission.Commons.FieldTheory.RatFunc.ordAtT_def

namespace Commons.FieldTheory.RatFunc

open Classical
open Commons.FieldTheory.RatFunc

/-- `ordAtT` is `⊤` exactly on the zero function. -/
theorem ordAtT_eq_top_iff {K : Type*} [Field K] {α : K} {x : RatFunc K} :
    ordAtT α x = ⊤ ↔ x = 0 := by
  by_cases hx : x = 0
  · subst hx
    simp [ordAtT]
  · rw [ordAtT_def α hx]
    simp [hx]

end Commons.FieldTheory.RatFunc
