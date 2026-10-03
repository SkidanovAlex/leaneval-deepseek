import Mathlib

/-!
# The image of a circle under an exterior holomorphic function has zero area

If `g` is holomorphic on the exterior `{1 < ‖z‖}` of the unit disc and `r > 1`, then the image of
the circle `‖z‖ = r` has two-dimensional Lebesgue measure zero.

The sphere `‖z‖ = r` is a null set for the two-dimensional Haar measure on `ℂ`
(`MeasureTheory.Measure.addHaar_sphere`), and `g` is differentiable at every point of it
(analyticity on the exterior, which the sphere lies in). Mathlib's
`MeasureTheory.addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero` then transfers the
nullity to the image. No regularity of the image beyond this is needed: the map need only be
differentiable on the null set itself.
-/

namespace Work.Repel.Koebe

theorem volume_image_sphere_eq_zero {g : ℂ → ℂ} {r : ℝ} (hr : 1 < r)
    (hg : ∀ z : ℂ, 1 < ‖z‖ → AnalyticAt ℂ g z) :
    MeasureTheory.volume (g '' Metric.sphere (0 : ℂ) r) = 0 := by
  have hs : MeasureTheory.volume (Metric.sphere (0 : ℂ) r) = 0 :=
    MeasureTheory.Measure.addHaar_sphere MeasureTheory.volume (0 : ℂ) r
  refine MeasureTheory.addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero
    (μ := MeasureTheory.volume) (f := g) (s := Metric.sphere (0 : ℂ) r) ?_ hs
  intro w hw
  have hwn : ‖w‖ = r := by simpa [Metric.mem_sphere, dist_eq_norm] using hw
  exact ((hg w (by rw [hwn]; exact hr)).restrictScalars (𝕜 := ℝ)).differentiableAt
    |>.differentiableWithinAt

end Work.Repel.Koebe
