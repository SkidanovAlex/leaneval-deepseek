import Mathlib
import Submission.Work.ELTop.Defs

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.ELTop

/-- The region of a ray polygon is open as soon as its boundary `polyCurve` is closed:
it is the connected component, in the open set `(polyCurve ps R)ᶜ`, of the reference ray point,
and connected components of open sets are open in a locally connected space such as `ℂ`. -/
theorem isOpen_polyRegion {c : ℂ} {φ : ℂ → ℂ} (hN : Work.EL.DynB c φ)
    (ps : List (Work.EL.CoPair hN)) (R : ℝ) (hcl : IsClosed (Work.EL.polyCurve ps R)) :
    IsOpen (Work.EL.polyRegion ps R) := by
  rw [Work.EL.polyRegion]
  exact hcl.isOpen_compl.connectedComponentIn

end Work.ELTop
