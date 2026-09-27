import Mathlib
import Submission.Work.Drive.UmlaufSetup

namespace Work.Drive

open scoped Manifold ContDiff
open Manifold

/-- The derivative of the plane curve `t ↦ γ (Circle.exp t)` of a smooth embedded closed plane
curve is `2π`-periodic.

The functions `t ↦ curve γ (t + 2π)` and `curve γ` are equal (`Circle.exp_add_two_pi`), so their
derivatives agree, and by the chain rule with the translation `t ↦ t + 2π`,
`deriv (fun t => curve γ (t + 2π)) t = deriv (curve γ) (t + 2π)`; the differentiability hypothesis
of the chain rule is available (`ContDiff ℝ 1 (curve γ)` from `hγ` composed with
`contMDiff_circleExp`, then `ContMDiff.contDiff`). -/
theorem deriv_curve_periodic (γ : Circle → ℝ × ℝ)
    (hγ : IsSmoothEmbedding (𝓡 1) (𝓘(ℝ, ℝ × ℝ)) ∞ γ) (t : ℝ) :
    deriv (Work.Drive.curve γ) (t + 2 * Real.pi) = deriv (Work.Drive.curve γ) t := by
  -- the translate of `curve γ` by `2π` agrees with `curve γ` pointwise
  have hfun : (fun x : ℝ => Work.Drive.curve γ (x + 2 * Real.pi)) = Work.Drive.curve γ := by
    funext x
    simp only [Work.Drive.curve]
    rw [Circle.exp_add_two_pi x]
  -- hence their derivatives agree
  have h := congrArg (fun g : ℝ → ℝ × ℝ => deriv g t) hfun
  -- and the chain rule with the translation `x ↦ x + 2π` identifies the derivative of the
  -- translate at `t` with the derivative of `curve γ` at `t + 2π`
  rw [deriv_comp_add_const] at h
  exact h

end Work.Drive
