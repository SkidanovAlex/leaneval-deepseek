import Mathlib

set_option linter.unusedVariables false

namespace Work.Smooth.Morse.MorseModel

/-- Mean-value inequality: if the derivative of `u` stays within `ε` of a fixed
continuous linear map `A` on the closed unit ball, then `u` is `ε`-close to
`u 0 + A ·` there.  This is the quantitative form of "a function with derivative
close to a constant is close to an affine function". -/
theorem norm_sub_linear_le {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {u : ℂ → F} {A : ℂ →L[ℝ] F} {ε : ℝ} (hε : 0 ≤ ε)
    (hdiff : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, HasFDerivAt u (fderiv ℝ u z) z)
    (hbound : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, ‖fderiv ℝ u z - A‖ ≤ ε) :
    ∀ z ∈ Metric.closedBall (0 : ℂ) 1, ‖u z - u 0 - A z‖ ≤ ε * ‖z‖ := by
  intro z hz
  have h0 : (0 : ℂ) ∈ Metric.closedBall (0 : ℂ) 1 := by
    simp [Metric.mem_closedBall]
  have h := Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le' (𝕜 := ℝ)
      (f := u) (f' := fun w => fderiv ℝ u w) (φ := A) (C := ε)
      (s := Metric.closedBall (0 : ℂ) 1) (x := 0) (y := z)
      (fun w hw => (hdiff w hw).hasFDerivWithinAt)
      (fun w hw => hbound w hw)
      (convex_closedBall 0 1) h0 hz
  simpa using h

end Work.Smooth.Morse.MorseModel
