import Mathlib
import Submission.Work.RatHurewicz.AttachCells

set_option synthInstance.maxHeartbeats 400000

/-!
# Every point of a cell attachment is joined to the old space

Let `attachCells n Y ι f` be the space obtained from `Y` by attaching `(n+2)`-cells along the
attaching maps `f : ι → C(S^{n+1}, Y)` (see `Submission/Work/RatHurewicz/AttachCells.lean`), and
let `attachIncl n Y ι f : C(Y, attachCells n Y ι f)` be the inclusion of the old space.

**`exists_joined_attachIncl`**: every point `p` of the attachment is joined, by a path in
`attachCells n Y ι f`, to a point of the image of `attachIncl`.

Points coming from `Y` are handled by reflexivity.  A point `(i, x)` of the `i`-th cell is joined
inside that cell to a boundary point (the closed disc is convex, hence path connected), and the
boundary of the `i`-th cell is glued to `Y` along `f i` by `attachIncl_attachRel`.

This is the `π₀`-statement for the Postnikov models of `Work.RatHurewicz` (blueprint §2, C0).
-/

open scoped Topology unitInterval

namespace Work.Serre

/-- The model disc `D^{n+2}` is path connected, being convex. -/
theorem pathConnectedSpace_cellDisk (n : ℕ) : PathConnectedSpace (Work.RatHurewicz.cellDisk n) :=
  isPathConnected_iff_pathConnectedSpace.mp
    ((convex_closedBall (0 : EuclideanSpace ℝ (Fin (n + 2))) 1).isPathConnected
      ⟨0, by simp [Metric.mem_closedBall]⟩)

/-- **Every point of `attachCells n Y ι f` is joined to the image of `Y`.** -/
theorem exists_joined_attachIncl (n : ℕ) (Y : Type) [TopologicalSpace Y] (ι : Type)
    (f : ι → C(Work.RatHurewicz.cellSphere n, Y)) (p : Work.RatHurewicz.attachCells n Y ι f) :
    ∃ y : Y, Joined p (Work.RatHurewicz.attachIncl n Y ι f y) := by
  refine Quotient.inductionOn' p ?_
  intro a
  rcases a with y | ⟨i, x⟩
  · exact ⟨y, Joined.refl _⟩
  · let z : Work.RatHurewicz.cellSphere n :=
      ⟨EuclideanSpace.single 0 (1 : ℝ), by
        rw [Metric.mem_sphere, dist_eq_norm]
        simp⟩
    have hp : Joined x (Work.RatHurewicz.cellSphereToDisk n z) :=
      (pathConnectedSpace_cellDisk n).joined x _
    have hcell := hp.map (Work.RatHurewicz.cellMap n Y ι f i).continuous
    refine ⟨f i z, ?_⟩
    rw [← Work.RatHurewicz.attachIncl_attachRel n Y ι f i z] at hcell
    exact hcell

end Work.Serre
