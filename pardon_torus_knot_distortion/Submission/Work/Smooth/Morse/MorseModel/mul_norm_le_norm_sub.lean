import Mathlib

set_option linter.unusedVariables false

namespace Work.Smooth.Morse.MorseModel

/-- Quantitative injectivity bound for a map `u` on the unit ball whose derivative is
uniformly close to an injective linear map `A` (with lower bound `c`): for `z` in the unit
ball, `(c - ε) * ‖z‖ ≤ ‖u z - u 0‖`.

The proof is the mean value inequality applied to `z ↦ u z - A z`, whose derivative
`fderiv ℝ u z - A` is bounded by `ε` on the (convex) unit ball. -/
theorem mul_norm_le_norm_sub {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {u : ℂ → F} {x : F} {A : ℂ →L[ℝ] F} {c ε : ℝ}
    (hc : 0 < c) (hε : 0 ≤ ε) (hAc : ∀ v : ℂ, c * ‖v‖ ≤ ‖A v‖) (h0 : u 0 = x)
    (hdiff : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, HasFDerivAt u (fderiv ℝ u z) z)
    (hbound : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, ‖fderiv ℝ u z - A‖ ≤ ε) :
    ∀ z ∈ Metric.closedBall (0 : ℂ) 1, (c - ε) * ‖z‖ ≤ ‖u z - x‖ := by
  intro z hz
  have hs : Convex ℝ (Metric.closedBall (0 : ℂ) 1) := convex_closedBall 0 1
  have hmem0 : (0 : ℂ) ∈ Metric.closedBall (0 : ℂ) 1 := by simp
  -- mean value inequality for `w ↦ u w - A w`
  have hd : ∀ w ∈ Metric.closedBall (0 : ℂ) 1,
      HasFDerivWithinAt (fun w => u w - A w) (fderiv ℝ u w - A) (Metric.closedBall (0 : ℂ) 1) w := by
    intro w hw
    exact ((hdiff w hw).hasFDerivWithinAt).sub (A.hasFDerivWithinAt)
  have hmvt := hs.norm_image_sub_le_of_norm_hasFDerivWithin_le hd hbound hmem0 hz
  have hsub : ‖u z - x - A z‖ ≤ ε * ‖z‖ := by
    have h := hmvt
    rw [h0, map_zero, sub_zero] at h
    rw [sub_zero, show u z - A z - x = u z - x - A z from by abel] at h
    exact h
  have h2 : ‖A z‖ ≤ ‖u z - x‖ + ε * ‖z‖ := by
    have h := norm_add_le (A z - (u z - x)) (u z - x)
    rw [show A z - (u z - x) + (u z - x) = A z from by abel] at h
    have he : ‖A z - (u z - x)‖ = ‖u z - x - A z‖ := norm_sub_rev (A z) (u z - x)
    linarith
  have h1 : c * ‖z‖ ≤ ‖u z - x‖ + ε * ‖z‖ := le_trans (hAc z) h2
  nlinarith [norm_nonneg z, norm_nonneg (u z - x)]

end Work.Smooth.Morse.MorseModel
