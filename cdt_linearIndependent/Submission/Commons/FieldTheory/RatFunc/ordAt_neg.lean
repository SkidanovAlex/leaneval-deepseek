import Mathlib
import Submission.Commons.FieldTheory.RatFunc.ordAt_def
import Submission.Commons.FieldTheory.RatFunc.ordAt_mul
import Submission.Commons.FieldTheory.RatFunc.ordAt_one

namespace Commons.FieldTheory.RatFunc

/-- The order of vanishing of `-x` equals that of `x`. -/
theorem ordAt_neg {K : Type*} [Field K] (α : K) (x : RatFunc K) : ordAt α (-x) = ordAt α x := by
  rcases eq_or_ne x 0 with rfl | hx
  · rw [neg_zero]
  · -- `-1` is a unit, so it does not change the order of vanishing.
    have h1 : ordAt α (-1 : RatFunc K) = 0 := by
      have h := ordAt_mul α (x := (-1 : RatFunc K)) (y := (-1 : RatFunc K))
        (by simp) (by simp)
      rw [show (-1 : RatFunc K) * (-1) = 1 by ring, ordAt_one] at h
      linarith
    calc ordAt α (-x) = ordAt α ((-1 : RatFunc K) * x) := by rw [neg_one_mul]
      _ = ordAt α (-1) + ordAt α x := ordAt_mul α (by simp) hx
      _ = ordAt α x := by rw [h1, zero_add]

end Commons.FieldTheory.RatFunc
