import Mathlib
import Submission.Work.Repel.deriv_lower_aux

/-!
# Lower bound for the derivative of a holomorphic injection on a disc (rescaled)

For a holomorphic injection `f` on `ball c R`, the derivative is bounded below by `‖deriv f c‖/12`
on the half-ball `closedBall c (R / 2)`.  This is a weak form of the lower half of Koebe's
distortion theorem, obtained from Bieberbach's second coefficient inequality (hence from
Grönwall's area theorem) by way of the Koebe transform and an integration of the resulting bound
on the logarithmic derivative.
-/

namespace Work.Repel

theorem deriv_lower_scaled {f : ℂ → ℂ} {c : ℂ} {R : ℝ} (hR : 0 < R)
    (hf : DifferentiableOn ℂ f (Metric.closedBall c R))
    (hinj : Set.InjOn f (Metric.ball c R)) :
    ∀ z ∈ Metric.closedBall c (R / 2), (1 / 12 : ℝ) * ‖deriv f c‖ ≤ ‖deriv f z‖ :=
  deriv_lower_aux hR hf hinj

end Work.Repel
