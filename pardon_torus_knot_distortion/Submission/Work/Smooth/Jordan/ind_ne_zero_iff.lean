import Mathlib
import Submission.Work.Smooth.Jordan.JordanIndex

namespace Work.Smooth.Jordan

/-- **The index form of Jordan separation, bounded side**: a point off the trace of a simple closed
`C¹` curve has nonzero index exactly when it lies on the bounded side `V` of the separation.

This is the companion of `Work.Smooth.Jordan.ind_eq_zero_iff` (`ind = 0 ↔ x ∈ U`); both are
immediate from the two clauses of the classical input `PlaneJordanSchoenflies` giving the value of
the index on the two sides together with the fact that `U ∪ V` exhausts the complement of the trace. -/
theorem ind_ne_zero_iff (c : SmoothPlaneCurve) (h : PlaneJordanSchoenflies c) {x : ℂ} (hx : x ∉ c.trace) : ind c x ≠ 0 ↔ x ∈ h.sep.V := by
  constructor
  · intro hne
    by_contra hxV
    have hxU : x ∈ h.sep.U := by
      have hmem : x ∈ h.sep.U ∪ h.sep.V := by
        rw [h.sep.union_eq]
        simpa using hx
      rcases hmem with h' | h'
      · exact h'
      · exact absurd h' hxV
    exact hne (h.ind_eq_zero_U x hxU)
  · intro hxV
    exact h.ind_ne_zero_V hxV

end Work.Smooth.Jordan
