import Mathlib
import Submission.Commons.FieldTheory.RatFunc.ordAtT_def
import Submission.Commons.FieldTheory.RatFunc.min_ordAt_le_ordAt_add

namespace Commons.FieldTheory.RatFunc

open Classical
open Commons.FieldTheory.RatFunc

/-- The `min` rule for `ordAtT`, with no side condition. -/
theorem ordAtT_add_ge {K : Type*} [Field K] (α : K) (x y : RatFunc K) :
    min (ordAtT α x) (ordAtT α y) ≤ ordAtT α (x + y) := by
  rcases eq_or_ne x 0 with rfl | hx
  · rw [zero_add]
    simp [ordAtT]
  rcases eq_or_ne y 0 with rfl | hy
  · rw [add_zero]
    simp [ordAtT]
  rcases eq_or_ne (x + y) 0 with hxy | hxy
  · rw [hxy]
    have : ordAtT α (0 : RatFunc K) = ⊤ := by simp [ordAtT]
    rw [this]
    exact le_top
  · rw [ordAtT_def α hx, ordAtT_def α hy, ordAtT_def α hxy]
    exact_mod_cast min_ordAt_le_ordAt_add α hxy

end Commons.FieldTheory.RatFunc
