import Mathlib

namespace Work.WilE2

/-- The complement of a (`Lebesgue`-)null subset of `Fin n → ℝ` is dense: every ball of
positive radius contains a point outside `N`.

This is the standard fact that `volume` on `Fin n → ℝ` is an open-positive measure (a nonempty
open set has positive measure), while `MeasureTheory.volume N = 0`; hence no ball of positive
radius can be contained in `N`. -/
theorem avoid_null {n : ℕ} {N : Set (Fin n → ℝ)} (hN : MeasureTheory.volume N = 0) (y : Fin n → ℝ) {ε : ℝ} (hε : 0 < ε) : ∃ y', dist y' y < ε ∧ y' ∉ N := by
  by_contra h
  -- `h` says every point of the ball lies in `N`
  push Not at h
  have hball : Metric.ball y ε ⊆ N := fun x hx => h x (by simpa [dist_comm] using hx)
  -- a ball of positive radius has positive Lebesgue measure
  have hpos : 0 < MeasureTheory.volume (Metric.ball y ε) :=
    Metric.measure_ball_pos MeasureTheory.volume y hε
  -- but it is contained in the null set `N`
  have hle : MeasureTheory.volume (Metric.ball y ε) ≤ 0 := by
    rw [← hN]
    exact MeasureTheory.measure_mono hball
  exact absurd hle (not_le.mpr hpos)

end Work.WilE2
