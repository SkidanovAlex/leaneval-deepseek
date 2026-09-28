import Mathlib
import Submission.Work.Serre.Wedge.Defs
import Submission.Work.Serre.cubeDiskHomeo

set_option synthInstance.maxHeartbeats 400000

/-!
# The cell classes of the wedge of spheres

The wedge `wX n S` (`Submission/Work/Serre/Wedge/Defs.lean`) is obtained from a point by attaching
`|S|`-many `(n+2)`-cells along the constant maps.  For `s : S` this file produces the cube
`I^{n+2} → wX n S` carried by the `s`-th cell (through the cube/disc homeomorphism
`Work.Serre.cubeDiskHomeo`) and its homotopy class `wCellClass s ∈ π_{n+2}(wX n S)`.

These cell classes are the generators of `π_{n+2}` of the wedge (the statement
`Work.StemsB.wedge_cellClass_generate`, proved in `Submission.Work.StemsB.wedgeCellGenerates`).
-/

namespace Work.StemsB

open CategoryTheory CategoryTheory.Limits
open scoped Topology Topology.Homotopy unitInterval

noncomputable section

/-- **The `s`-th cell of the wedge, as a cube.** -/
def wCellCube {n : ℕ} (S : Type) (s : S) :
    C(Work.Stems.Cubical.IC (n + 2), Work.Serre.Wedge.wX n S) :=
  (Work.RatHurewicz.cellMap n PUnit S (Work.Serre.Wedge.wF n S) s).comp
    ⟨⇑(Classical.choose (Work.Serre.cubeDiskHomeo (n + 2))),
      (Classical.choose (Work.Serre.cubeDiskHomeo (n + 2))).continuous⟩

/-- The cube of the `s`-th cell is constant on the boundary of the cube, with value the base point
of the wedge (the boundary condition of `Work.Serre.CWModel.genStep`). -/
theorem wCellCube_boundary {n : ℕ} (S : Type) (s : S) (x : Work.Stems.Cubical.IC (n + 2))
    (hx : x ∈ Cube.boundary (Fin (n + 2))) :
    wCellCube S s x = Work.Serre.Wedge.wB n S := by
  have hxb : ((Classical.choose (Work.Serre.cubeDiskHomeo (n + 2))) x :
      EuclideanSpace ℝ (Fin (n + 2))) ∈ Metric.sphere 0 1 :=
    (Classical.choose_spec (Work.Serre.cubeDiskHomeo (n + 2)) x).mp hx
  have hcell : (Work.RatHurewicz.cellMap n PUnit S (Work.Serre.Wedge.wF n S) s)
      ((Classical.choose (Work.Serre.cubeDiskHomeo (n + 2))) x)
      = Work.RatHurewicz.attachIncl n PUnit S (Work.Serre.Wedge.wF n S)
          ((Work.Serre.Wedge.wF n S s) ⟨(Classical.choose (Work.Serre.cubeDiskHomeo (n + 2))) x,
            hxb⟩) :=
    (Work.RatHurewicz.attachIncl_attachRel n PUnit S (Work.Serre.Wedge.wF n S) s
      ⟨(Classical.choose (Work.Serre.cubeDiskHomeo (n + 2))) x, hxb⟩).symm
  show (Work.RatHurewicz.cellMap n PUnit S (Work.Serre.Wedge.wF n S) s)
      ((Classical.choose (Work.Serre.cubeDiskHomeo (n + 2))) x) = _
  rw [hcell]
  rfl

/-- **The class of the `s`-th cell in `π_{n+2}` of the wedge.** -/
def wCellClass {n : ℕ} (S : Type) (s : S) :
    HomotopyGroup (Fin (n + 2)) (Work.Serre.Wedge.wX n S) (Work.Serre.Wedge.wB n S) :=
  Quotient.mk _ (⟨wCellCube S s, wCellCube_boundary S s⟩ :
    Ω^ (Fin (n + 2)) (Work.Serre.Wedge.wX n S) (Work.Serre.Wedge.wB n S))

end

end Work.StemsB
