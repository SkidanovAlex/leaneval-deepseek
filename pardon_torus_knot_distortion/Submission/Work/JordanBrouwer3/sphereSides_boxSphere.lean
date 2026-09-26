import Mathlib
import Submission.Work.JordanBrouwer3.Defs
import Submission.Work.Topology.SphereSlicing.Defs
import Submission.Work.Topology.SphereSlicing.frontier_PBox
import Submission.Work.Topology.SphereSlicing.convex_PBox
import Submission.Work.Topology.SphereSlicing.isOpen_PBox
import Submission.Work.JordanBrouwer3.sphereSides_of_convexFrontier

/-!
# The two sides of the box sphere `∂PBox s c σ`

Pardon's box `Submission.PBox s c σ` is the open convex box with centre `c` and side lengths
`boxSide i * s` in the coordinate directions `σ i`; its boundary is the *box sphere*
`Work.Topology.SphereSlicing.BoxSphere s c σ = {y | boxNorm c σ y = s}`.

Here we observe that the box sphere is the frontier of a compact convex body with nonempty
interior, namely `K = closure (PBox s c σ)`: consequently it has two sides in the sense of
`Work.JordanBrouwer3.SphereSides`, by `Work.JordanBrouwer3.sphereSides_of_convexFrontier`.

The only computation is `frontier K = BoxSphere s c σ`, which follows from

* `interior (closure (PBox s c σ)) = interior (PBox s c σ) = PBox s c σ` (convexity, see
  `Convex.interior_closure_eq_interior_of_nonempty_interior`, and openness of the box), and
* `frontier (PBox s c σ) = BoxSphere s c σ` (`Work.Topology.SphereSlicing.frontier_PBox`).
-/

open Set
open LeanEval.KnotTheory.PardonDistortion

namespace Work.JordanBrouwer3

/-- The box sphere `Work.Topology.SphereSlicing.BoxSphere s c σ` is the frontier of the compact
convex body `closure (Submission.PBox s c σ)`. -/
theorem frontier_closure_PBox {s : ℝ} (hs : 0 < s) (c : R3) (σ : Equiv.Perm (Fin 3)) :
    frontier (closure (Submission.PBox s c σ)) = Work.Topology.SphereSlicing.BoxSphere s c σ := by
  have hPBox_open : IsOpen (Submission.PBox s c σ) :=
    Work.Topology.SphereSlicing.isOpen_PBox s c σ
  have hPBox_cv : Convex ℝ (Submission.PBox s c σ) :=
    Work.Topology.SphereSlicing.convex_PBox s c σ
  have hc_mem : c ∈ Submission.PBox s c σ := by
    rw [Submission.mem_PBox]
    intro i
    rw [sub_self, abs_zero]
    exact mul_pos (Submission.boxSide_pos i) hs
  have hinter_ne : (interior (Submission.PBox s c σ)).Nonempty := by
    rw [hPBox_open.interior_eq]
    exact ⟨c, hc_mem⟩
  calc frontier (closure (Submission.PBox s c σ))
      = closure (Submission.PBox s c σ) \ interior (closure (Submission.PBox s c σ)) :=
        IsClosed.frontier_eq isClosed_closure
    _ = closure (Submission.PBox s c σ) \ interior (Submission.PBox s c σ) := by
        rw [hPBox_cv.interior_closure_eq_interior_of_nonempty_interior hinter_ne]
    _ = closure (Submission.PBox s c σ) \ Submission.PBox s c σ := by
        rw [hPBox_open.interior_eq]
    _ = frontier (Submission.PBox s c σ) := (IsOpen.frontier_eq hPBox_open).symm
    _ = Work.Topology.SphereSlicing.BoxSphere s c σ :=
        Work.Topology.SphereSlicing.frontier_PBox hs c σ

theorem sphereSides_boxSphere {s : ℝ} (hs : 0 < s) (c : LeanEval.KnotTheory.PardonDistortion.R3)
    (σ : Equiv.Perm (Fin 3)) :
    Nonempty (Work.JordanBrouwer3.SphereSides (Work.Topology.SphereSlicing.BoxSphere s c σ)) := by
  have hPBox_open : IsOpen (Submission.PBox s c σ) :=
    Work.Topology.SphereSlicing.isOpen_PBox s c σ
  have hPBox_cv : Convex ℝ (Submission.PBox s c σ) :=
    Work.Topology.SphereSlicing.convex_PBox s c σ
  have hc_mem : c ∈ Submission.PBox s c σ := by
    rw [Submission.mem_PBox]
    intro i
    rw [sub_self, abs_zero]
    exact mul_pos (Submission.boxSide_pos i) hs
  -- The compact convex body whose frontier is the box sphere.
  have hKc : IsCompact (closure (Submission.PBox s c σ)) := by
    refine IsCompact.of_isClosed_subset (isCompact_closedBall c ((5 / 2) * s)) isClosed_closure ?_
    refine closure_minimal ?_ Metric.isClosed_closedBall
    exact (Submission.PBox_subset_ball s (le_of_lt hs) c σ).trans Metric.ball_subset_closedBall
  have hKcv : Convex ℝ (closure (Submission.PBox s c σ)) := hPBox_cv.closure
  have hKi : (interior (closure (Submission.PBox s c σ))).Nonempty :=
    ⟨c, hPBox_open.subset_interior_closure hc_mem⟩
  have hsides := Work.JordanBrouwer3.sphereSides_of_convexFrontier hKc hKcv hKi
  rwa [frontier_closure_PBox hs c σ] at hsides

end Work.JordanBrouwer3
