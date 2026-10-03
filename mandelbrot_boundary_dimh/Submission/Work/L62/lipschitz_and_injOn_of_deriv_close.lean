import Mathlib

namespace Work.L62

set_option linter.unusedVariables false in
/-- **Lemma 6.2 helper (L62).** If a holomorphic map `S : ℂ → ℂ` has `‖S' - 1‖ ≤ k < 1` on a
closed ball, then `w ↦ S w - w` is `k`-Lipschitz there, and `S` is injective on the ball.

The Lipschitz bound is the mean value inequality applied to `F w = S w - w` (whose derivative is
`S' w - 1`) on the convex set `closedBall z R₀`; injectivity follows because `S a = S b` forces
`‖a - b‖ = ‖(S a - a) - (S b - b)‖ ≤ k ‖a - b‖` and `k < 1`. -/
theorem lipschitz_and_injOn_of_deriv_close {S : ℂ → ℂ} {z : ℂ} {R₀ k : ℝ}
    (hk0 : 0 ≤ k) (hk1 : k < 1)
    (hSdiff : ∀ w ∈ Metric.closedBall z R₀, DifferentiableAt ℂ S w)
    (hSderiv : ∀ w ∈ Metric.closedBall z R₀, ‖deriv S w - 1‖ ≤ k) :
    (∀ a ∈ Metric.closedBall z R₀, ∀ b ∈ Metric.closedBall z R₀,
        ‖(S a - a) - (S b - b)‖ ≤ k * ‖a - b‖) ∧
      Set.InjOn S (Metric.closedBall z R₀) := by
  have hs : Convex ℝ (Metric.closedBall z R₀) := convex_closedBall z R₀
  have hf : ∀ x ∈ Metric.closedBall z R₀,
      HasDerivWithinAt (fun w => S w - w) (deriv S x - 1) (Metric.closedBall z R₀) x := by
    intro x hx
    exact ((hSdiff x hx).hasDerivAt.sub (hasDerivAt_id x)).hasDerivWithinAt
  have hlip : ∀ a ∈ Metric.closedBall z R₀, ∀ b ∈ Metric.closedBall z R₀,
      ‖(S a - a) - (S b - b)‖ ≤ k * ‖a - b‖ := by
    intro a ha b hb
    exact Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hf hSderiv hs hb ha
  refine ⟨hlip, ?_⟩
  intro a ha b hb hab
  have h1 := hlip a ha b hb
  have hEq : (S a - a) - (S b - b) = b - a := by rw [hab]; ring
  have h2 : ‖a - b‖ ≤ k * ‖a - b‖ := by
    have := h1
    rw [hEq, norm_sub_rev] at this
    exact this
  have h4 : ‖a - b‖ = 0 := by nlinarith [h2, norm_nonneg (a - b), hk0, hk1]
  exact sub_eq_zero.mp (norm_eq_zero.mp h4)

end Work.L62
