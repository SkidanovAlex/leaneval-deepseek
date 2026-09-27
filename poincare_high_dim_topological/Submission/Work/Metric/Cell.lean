/-
Copyright (c) 2024 The poincare_high_dim_topological team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Submission.Work.Metric.Basic
import Submission.Work.Metric.nonempty_chartBall_homeomorph_space
import Submission.Work.Metric.nonempty_chartBall_homeomorph_unitBall

/-!
# Chart balls are open cells

Every member of a `Work.Metric.ChartBallCover` of a charted space over a real normed space is
homeomorphic to the whole model space, hence is an open cell.  This is the property used by the
cell-covering (Newman) step of the engulfing proof.
-/

open Set Metric

namespace Work.Metric

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace E M]

/-- Every chart ball of a chart ball cover is homeomorphic to the model space `E`. -/
theorem ChartBallCover.nonempty_chartBall_homeomorph_space (C : ChartBallCover E M) (i : C.ι) :
    Nonempty (chartBall (E := E) (C.center i) (C.radius i) ≃ₜ E) :=
  Work.Metric.nonempty_chartBall_homeomorph_space (C.radius_pos i)
    (ball_subset_target_of_closedBall_subset_target (C.closedBall_subset_target i))

/-- Every point of a charted space over a real normed space has an open neighbourhood
homeomorphic to the whole model space (the space is locally Euclidean). -/
theorem exists_homeomorph_mem_nhds (x : M) : ∃ U ∈ nhds x, Nonempty (U ≃ₜ E) := by
  obtain ⟨r, hr, hrt, -⟩ :=
    exists_chartBall_subset_of_mem_nhds (E := E) (Filter.univ_mem (f := nhds x))
  have hball := ball_subset_target_of_closedBall_subset_target hrt
  exact ⟨chartBall (E := E) x r, (isOpen_chartBall hball).mem_nhds (mem_chartBall_self hr),
    nonempty_chartBall_homeomorph_space hr hball⟩

/-- Every chart ball of a chart ball cover is homeomorphic to the unit ball of the model space. -/
theorem ChartBallCover.nonempty_chartBall_homeomorph_unitBall (C : ChartBallCover E M) (i : C.ι) :
    Nonempty (chartBall (E := E) (C.center i) (C.radius i) ≃ₜ ball (0 : E) 1) :=
  Work.Metric.nonempty_chartBall_homeomorph_unitBall (C.radius_pos i)
    (ball_subset_target_of_closedBall_subset_target (C.closedBall_subset_target i))

end Work.Metric
