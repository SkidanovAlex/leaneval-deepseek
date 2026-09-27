import Mathlib
import Submission.Work.Metric.Basic

namespace Work.Metric

/-- A chart ball is homeomorphic to the whole model space: the chart identifies it with an open
ball of positive radius, and any open ball of positive radius in a real normed space is
homeomorphic to the space. -/
theorem nonempty_chartBall_homeomorph_space {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {M : Type*} [TopologicalSpace M] [ChartedSpace E M] {x : M} {r : ℝ} (hr : 0 < r)
    (h : Metric.ball (chartAt E x x) r ⊆ (chartAt E x).target) :
    Nonempty (Work.Metric.chartBall (E := E) x r ≃ₜ E) := by
  refine ⟨(chartBallHomeomorph h).trans ?_⟩
  exact (((Homeomorph.unitBall (E := E)).trans
    (OpenPartialHomeomorph.unitBallBall (chartAt E x x) r hr).toHomeomorphSourceTarget)).symm

end Work.Metric
