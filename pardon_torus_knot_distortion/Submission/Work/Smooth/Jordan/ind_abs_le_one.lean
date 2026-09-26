import Mathlib
import Submission.Work.Smooth.Jordan.JordanIndex

namespace Work.Smooth.Jordan

/-- **The index of a simple closed curve has modulus at most `1` off the curve.**
Every point off the trace lies on one of the two sides of the Jordan separation: on the unbounded
side `U` the index vanishes, and on the bounded side `V` its modulus is `1`. -/
theorem ind_abs_le_one (c : SmoothPlaneCurve) (h : PlaneJordanSchoenflies c) {x : ℂ}
    (hx : x ∉ c.trace) : |ind c x| ≤ 1 := by
  have hmem : x ∈ h.sep.U ∪ h.sep.V := by
    rw [h.sep.union_eq]
    exact hx
  rcases hmem with hU | hV
  · rw [h.ind_eq_zero_U x hU]; norm_num
  · rw [h.ind_abs_eq_one_V x hV]

end Work.Smooth.Jordan
