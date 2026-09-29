import Mathlib
import Submission.Work.TMComp.Kotani.ExtOnShift

namespace Work.TMComp.Kotani

/-- If `f` is analytic and nowhere zero on the ball of radius `r` around `star c`, then
`w ↦ 1 / star (f (star w))` is analytic on the ball of radius `r` around `c`.

The key point is that `star ∘ f ∘ star` is complex differentiable -- and hence analytic -- by
`DifferentiableAt.star_star` (a `star`-conjugation is complex differentiable for functions on `ℂ`,
even though `star` itself is only anti-holomorphic: the two conjugations cancel), and that its
values are again nowhere zero because `star` is injective. -/
theorem analyticOnNhd_inv_star_conj_center {c : ℂ} {r : ℝ} {f : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f (Metric.ball (star c) r))
    (hnz : ∀ u ∈ Metric.ball (star c) r, f u ≠ 0) :
    AnalyticOnNhd ℂ (fun w : ℂ => 1 / star (f (star w))) (Metric.ball c r) := by
  simp only [one_div]
  refine AnalyticOnNhd.inv ?_ ?_
  · apply DifferentiableOn.analyticOnNhd
    · intro w hw
      have hw' : star w ∈ Metric.ball (star c) r := by
        simpa [Metric.mem_ball] using hw
      have h2 := (hf (star w) hw').differentiableAt.star_star
      simpa [Function.comp_def] using h2.differentiableWithinAt
    · exact Metric.isOpen_ball
  · intro x hx
    have hx' : star x ∈ Metric.ball (star c) r := by
      simpa [Metric.mem_ball] using hx
    simpa [Function.comp_def] using hnz (star x) hx'

end Work.TMComp.Kotani
