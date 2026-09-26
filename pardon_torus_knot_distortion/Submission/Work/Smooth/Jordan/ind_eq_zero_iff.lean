import Mathlib
import Submission.Work.Smooth.Jordan.JordanIndex

namespace Work.Smooth.Jordan

theorem ind_eq_zero_iff (c : SmoothPlaneCurve) (h : PlaneJordanSchoenflies c) {x : ℂ} (hx : x ∉ c.trace) : ind c x = 0 ↔ x ∈ h.sep.U := by
  constructor
  · intro h0
    rw [h.sep.mem_iff hx]
    intro hxV
    exact h.ind_ne_zero_V hxV h0
  · intro hxU
    exact h.ind_eq_zero_U x hxU

end Work.Smooth.Jordan
