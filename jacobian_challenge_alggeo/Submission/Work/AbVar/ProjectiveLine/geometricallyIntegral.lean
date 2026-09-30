import Mathlib
import Submission.Work.AbVar.Basic
import Submission.Work.AbVar.ProjectiveLine
import Submission.Work.AbVar.SmoothReduced.geometricallyIntegral_of_smooth_of_geometricallyIrreducible
import Submission.Work.AbVar.P1Chart.Smooth
import Submission.Work.AbVar.ProjectiveLine.geometricallyIrreducible

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.AbVar.ProjectiveLine

open CategoryTheory in
theorem geometricallyIntegral {k : Type*} [Field k] :
    AlgebraicGeometry.GeometricallyIntegral (Work.AbVar.P1 k).hom := by
  haveI := Work.AbVar.P1Chart.smooth (k := k)
  haveI := Work.AbVar.ProjectiveLine.geometricallyIrreducible (k := k)
  exact Work.AbVar.SmoothReduced.geometricallyIntegral_of_smooth_of_geometricallyIrreducible _

end Work.AbVar.ProjectiveLine
