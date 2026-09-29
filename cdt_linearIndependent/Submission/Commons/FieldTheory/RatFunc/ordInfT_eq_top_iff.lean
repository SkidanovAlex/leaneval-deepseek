import Mathlib
import Submission.Commons.FieldTheory.RatFunc.ordInfT_def

namespace Commons.FieldTheory.RatFunc

/-- `ordInfT` is `⊤` exactly at zero. -/
theorem ordInfT_eq_top_iff {K : Type*} [Field K] {x : RatFunc K} :
    ordInfT x = ⊤ ↔ x = 0 := by
  constructor
  · intro h
    by_contra hx
    rw [ordInfT_def hx] at h
    exact WithTop.coe_ne_top h
  · rintro rfl
    simp [ordInfT]

end Commons.FieldTheory.RatFunc
