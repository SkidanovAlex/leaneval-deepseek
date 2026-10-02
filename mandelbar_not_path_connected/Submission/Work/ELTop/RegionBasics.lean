/-
# ELTop: elementary consequences of "the region is the bounded side"

`polyRegion_eq_bounded_side` identifies the region of a ray polygon with the bounded side of the
Jordan curve `polyCurve`; this file records the consequences that callers use most often:
the region is nonempty, bounded, and its frontier is the polygon.
-/
import Submission.Work.ELTop.Defs
import Submission.Work.ELTop.polyRegion_eq_bounded_side
import Submission.Work.ELTop.seed_mem_polyRegion

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open Classical Filter Set
open scoped Topology

set_option linter.unusedVariables false

noncomputable section

namespace Work.ELTop

/-- The region of a ray polygon is nonempty. -/
theorem polyRegion_nonempty {c : ℂ} {φ : ℂ → ℂ} (hN : Work.EL.DynB c φ)
    (ps : List (Work.EL.CoPair hN)) (hA : Work.EL.PolyAdmissible ps) {R : ℝ} (hR : 1 < R) :
    (Work.EL.polyRegion ps R).Nonempty :=
  ⟨_, seed_mem_polyRegion hN ps hA hR⟩

/-- The region of a ray polygon is bounded. -/
theorem isBounded_polyRegion {c : ℂ} {φ : ℂ → ℂ} (hN : Work.EL.DynB c φ)
    (hJ : Work.Top.JordanForm) (ps : List (Work.EL.CoPair hN)) (hA : Work.EL.PolyAdmissible ps)
    {R : ℝ} (hR : 1 < R) (hC : Work.Top.IsJordanCurve (Work.EL.polyCurve ps R)) :
    Bornology.IsBounded (Work.EL.polyRegion ps R) := by
  obtain ⟨S, hS⟩ := polyRegion_eq_bounded_side hN hJ ps hA hR hC
  rw [hS]; exact S.bounded_I

/-- The frontier of the region of a ray polygon is the polygon itself. -/
theorem frontier_polyRegion_eq_polyCurve {c : ℂ} {φ : ℂ → ℂ} (hN : Work.EL.DynB c φ)
    (hJ : Work.Top.JordanForm) (ps : List (Work.EL.CoPair hN)) (hA : Work.EL.PolyAdmissible ps)
    {R : ℝ} (hR : 1 < R) (hC : Work.Top.IsJordanCurve (Work.EL.polyCurve ps R)) :
    frontier (Work.EL.polyRegion ps R) = Work.EL.polyCurve ps R := by
  obtain ⟨S, hS⟩ := polyRegion_eq_bounded_side hN hJ ps hA hR hC
  rw [hS]; exact S.frontier_I

/-- The closure of the region of a ray polygon is the region together with the polygon. -/
theorem closure_polyRegion_eq {c : ℂ} {φ : ℂ → ℂ} (hN : Work.EL.DynB c φ)
    (hJ : Work.Top.JordanForm) (ps : List (Work.EL.CoPair hN)) (hA : Work.EL.PolyAdmissible ps)
    {R : ℝ} (hR : 1 < R) (hC : Work.Top.IsJordanCurve (Work.EL.polyCurve ps R)) :
    closure (Work.EL.polyRegion ps R) = Work.EL.polyRegion ps R ∪ Work.EL.polyCurve ps R := by
  obtain ⟨S, hS⟩ := polyRegion_eq_bounded_side hN hJ ps hA hR hC
  rw [hS]
  rw [closure_eq_self_union_frontier, S.frontier_I]

end Work.ELTop
