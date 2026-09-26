import Mathlib
import Submission.Work.Topology.SphereSlicing.Defs
import Submission.Work.Topology.SphereSlicing.frontier_PBox

namespace Work.Topology.SphereSlicing

/-- The box sphere `BoxSphere s c σ` is the frontier of Pardon's box `PBox s c σ`
(`frontier_PBox`); a frontier is closed (`isClosed_frontier`) and lies in the closure of the box,
which is contained in the closed ball of radius `(5/2) s` about `c` because the box is contained
in the open ball of that radius (`Submission.PBox_subset_ball`).  Closed balls are compact in
`ℝ³`, so the box sphere is compact. -/
theorem isCompact_BoxSphere {s : ℝ} (hs : 0 < s) (c : LeanEval.KnotTheory.PardonDistortion.R3)
    (σ : Equiv.Perm (Fin 3)) :
    IsCompact (Work.Topology.SphereSlicing.BoxSphere s c σ) := by
  rw [← frontier_PBox hs c σ]
  refine (isCompact_closedBall c ((5 / 2) * s)).of_isClosed_subset isClosed_frontier ?_
  intro y hy
  exact closure_minimal
    ((Submission.PBox_subset_ball s (le_of_lt hs) c σ).trans Metric.ball_subset_closedBall)
    Metric.isClosed_closedBall (frontier_subset_closure hy)

end Work.Topology.SphereSlicing
