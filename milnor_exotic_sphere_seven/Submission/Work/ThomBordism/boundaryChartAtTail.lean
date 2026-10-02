import Mathlib
import Submission.Work.Surgery.Boundary
import Submission.Work.PTGeometric.FlatSource
import Submission.Work.PTGeometric.exists_halfOrientationFamily_of_det_pos

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# THOM: the canonical boundary chart is the tail of the interior chart

`Work.Surgery.boundaryChartAt (n) x` is the preferred chart of the boundary of a
`EuclideanHalfSpace (n+1)`-modelled manifold at a boundary point `x`.  This file records that it is
exactly the boundary chart *induced* by the structure's chart at `x`:

    Work.Surgery.boundaryChartAt ⟨y,hy⟩ z = Work.PTGeometric.tail n (extChartAt I y z.1)

i.e. its value is the tail (drop the `0`-th coordinate) of the interior chart.  This is what
discharges the `hcompat` hypothesis of the last mile's boundary-sign transfer
(`Submission/Work/ThomBordism/NOTE_SESSION91_UNIFORM_BOUNDARY_SIGN.md` §5), and it is the canonical
boundary chart in which the last mile's T1 side is to be read.

No `sorry`; no new axioms.
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

open CategoryTheory
open scoped Manifold Topology ContDiff

namespace Work.ThomBordism

open Work.PTGeometric

variable {n : ℕ} {W : TopCat} [T2Space W]
  [ChartedSpace (EuclideanHalfSpace (n + 1)) W]
  [IsManifold (modelWithCornersEuclideanHalfSpace (n + 1)) (∞ : WithTop ℕ∞) W]

/-- **The preferred boundary chart of a half-space manifold is the tail of the structure's chart.**

For a boundary point `y` and any boundary point `z` in the source of the structure's chart at `y`,
the value of `Work.Surgery.boundaryChartAt ⟨y, hy⟩` at `z` is `Work.PTGeometric.tail n` of the value
of that chart at `z`. -/
theorem boundaryChartAt_eq_tail_extChartAt (y : W)
    (hy : y ∈ (modelWithCornersEuclideanHalfSpace (n + 1)).boundary W) :
    ∀ z : ↥((modelWithCornersEuclideanHalfSpace (n + 1)).boundary W),
      z.1 ∈ (extChartAt (modelWithCornersEuclideanHalfSpace (n + 1)) y).source →
      Work.Surgery.boundaryChartAt (n := n) ⟨y, hy⟩ z
        = Work.PTGeometric.tail n
            (extChartAt (modelWithCornersEuclideanHalfSpace (n + 1)) y z.1) := by
  intro z hz
  have hmem : z ∈ (Work.Surgery.boundaryChartAt (n := n) ⟨y, hy⟩).source := by
    rw [Work.Surgery.boundaryChartAt_source]
    exact hz
  rw [Work.Surgery.boundaryChartAt_apply (n := n) ⟨y, hy⟩ z hmem]
  rfl

/-- **The preferred boundary chart's source contains its own centre.** -/
theorem boundaryChartAt_mem_source' (y : W)
    (hy : y ∈ (modelWithCornersEuclideanHalfSpace (n + 1)).boundary W) :
    (⟨y, hy⟩ : ↥((modelWithCornersEuclideanHalfSpace (n + 1)).boundary W)) ∈
      (Work.Surgery.boundaryChartAt (n := n) ⟨y, hy⟩).source :=
  Work.Surgery.boundaryChartAt_mem_source (n := n) ⟨y, hy⟩

end Work.ThomBordism
