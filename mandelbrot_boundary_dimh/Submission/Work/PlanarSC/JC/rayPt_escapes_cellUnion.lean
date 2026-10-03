import Mathlib
import Submission.Work.PlanarSC.JC.RayBasic
import Submission.Work.HornSC.CellBoundaryJordan.RayDefs

/-!
# The ray `t ↦ a + t(1 + εI)` escapes every finite union of lattice cells

`Work.HornSC.cellUnion A` is a finite union of closed unit lattice squares, hence compact, hence
bounded; while `(rayPt a ε t).re = a.re + t` tends to `+∞`.  So every such ray leaves
`cellUnion A` eventually.  This is the "escape" half of the odd-crossing parity argument for the
wall set of a polyomino.
-/

namespace Work.PlanarSC.JC

open Set

/-- A ray in the direction `1 + εI` eventually leaves `cellUnion A`: `cellUnion A` is bounded,
while the real part of `rayPt a ε t` is `a.re + t`, which tends to `+∞`. -/
theorem rayPt_escapes_cellUnion (A : Finset (ℤ × ℤ)) (a : ℂ) (ε : ℝ) :
    ∃ T : ℝ, ∀ t : ℝ, T ≤ t →
      Work.HornSC.CellBoundaryJordan.rayPt a ε t ∉ Work.HornSC.cellUnion A := by
  obtain ⟨R, hR⟩ := (Work.HornSC.isCompact_cellUnion A).isBounded.subset_closedBall (0 : ℂ)
  refine ⟨R + |a.re| + 1, ?_⟩
  intro t ht hmem
  have hb : ‖Work.HornSC.CellBoundaryJordan.rayPt a ε t‖ ≤ R := by
    simpa [Metric.mem_closedBall, dist_eq_norm] using hR hmem
  have hre : (Work.HornSC.CellBoundaryJordan.rayPt a ε t).re = a.re + t :=
    Work.HornSC.CellBoundaryJordan.rayPt_re a ε t
  have h1 : a.re + t ≤ ‖Work.HornSC.CellBoundaryJordan.rayPt a ε t‖ := by
    rw [← hre]; exact Complex.re_le_norm _
  have h2 : R < a.re + t := by
    have := neg_abs_le a.re
    linarith
  linarith

end Work.PlanarSC.JC
