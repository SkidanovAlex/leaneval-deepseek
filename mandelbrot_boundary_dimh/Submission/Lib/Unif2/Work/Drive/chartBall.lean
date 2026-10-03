import Mathlib

/-!
# Chart balls on a `ℂ`-charted space

`chartBall x r` is the set of points `y` whose coordinate in the chart at `x` lies in the open disc
of radius `r` around the coordinate of `x`.  This is exactly the set appearing in the statement of
`Work.Drive.exists_phase_chain`, isolated here so that it can be shared with the auxiliary lemmas
about the "chain to infinity".
-/

open Set Metric

namespace Work.Drive

/-- The chart ball of radius `r` around `x`. -/
def chartBall {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X] (x : X) (r : ℝ) : Set X :=
  {y : X | y ∈ (chartAt ℂ x).source ∧ (chartAt ℂ x) y ∈ Metric.ball ((chartAt ℂ x) x) r}

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]

theorem self_mem_chartBall {x : X} {r : ℝ} (hr : 0 < r) : x ∈ chartBall x r :=
  ⟨mem_chart_source ℂ x, Metric.mem_ball_self hr⟩

theorem chartBall_subset_source {x : X} {r : ℝ} : chartBall x r ⊆ (chartAt ℂ x).source :=
  fun _ hy => hy.1

theorem chartBall_mono {x : X} {r r' : ℝ} (hr : r ≤ r') : chartBall x r ⊆ chartBall x r' :=
  fun _ hy => ⟨hy.1, Metric.ball_subset_ball hr hy.2⟩

end Work.Drive
