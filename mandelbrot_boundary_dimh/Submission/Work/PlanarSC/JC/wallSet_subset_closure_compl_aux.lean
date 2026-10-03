import Mathlib
import Submission.Work.HornSC.CellBoundaryJordan.Defs
import Submission.Work.HornSC.Cells
import Submission.Work.HornSC.CellBoundaryJordan.frontier_cellUnion_eq_wallSet

/-!
# A wall point lies in the closure of the complement of the cell union

`Work.HornSC.cellUnion A` is the union of the closed unit cells `cell p`, `p ∈ A`, and
`Work.HornSC.CellBoundaryJordan.wallSet A` is the union of the closed unit grid segments that
separate a cell of `A` from a cell outside `A`.

A wall point lies on the frontier of `cellUnion A` (indeed
`frontier (cellUnion A) = wallSet A`, proved in
`Submission.Work.HornSC.CellBoundaryJordan.frontier_cellUnion_eq_wallSet`), hence in the closure of
its complement.
-/

namespace Work.PlanarSC.JC

theorem wallSet_subset_closure_compl_aux (A : Finset (ℤ × ℤ)) :
    Work.HornSC.CellBoundaryJordan.wallSet A ⊆ closure (Work.HornSC.cellUnion A)ᶜ := by
  intro z hz
  have h : z ∈ frontier (Work.HornSC.cellUnion A) := by
    rw [Work.HornSC.CellBoundaryJordan.frontier_cellUnion_eq_wallSet]
    exact hz
  rw [frontier_eq_closure_inter_closure] at h
  exact h.2

end Work.PlanarSC.JC
