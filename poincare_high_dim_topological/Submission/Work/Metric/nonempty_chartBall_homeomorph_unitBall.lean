import Mathlib
import Submission.Work.Metric.Basic

namespace Work.Metric

/-- A chart ball of positive radius is homeomorphic to the unit ball of the model space: it is
homeomorphic to the ball of radius `r` around `chartAt E x x` via the chart, and that ball is
homeomorphic to the unit ball by scaling and translation. -/
theorem nonempty_chartBall_homeomorph_unitBall {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {M : Type*} [TopologicalSpace M] [ChartedSpace E M] {x : M} {r : ℝ} (hr : 0 < r)
    (h : Metric.ball (chartAt E x x) r ⊆ (chartAt E x).target) :
    Nonempty (Work.Metric.chartBall (E := E) x r ≃ₜ Metric.ball (0 : E) 1) :=
  ⟨(chartBallHomeomorph h).trans
    (OpenPartialHomeomorph.unitBallBall (chartAt E x x) r hr).toHomeomorphSourceTarget.symm⟩

end Work.Metric
