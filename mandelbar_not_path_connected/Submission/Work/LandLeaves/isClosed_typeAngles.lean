import Mathlib
import Submission.Work.LandLeaves.Defs
import Submission.Work.LandLeaves.periodicAngle_of_landsAt_isRepelling
import Submission.Work.LandLeaves.isClosed_rayAccum_singleton
import Submission.Work.LANDCL.Defs

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.LandLeaves

/-- `typeAngles` is literally the set-builder set `{ψ | rayAccum c φ ψ = {y}}`. -/
theorem typeAngles_eq_setOf (c : ℂ) (φ : ℂ → ℂ) (y : ℂ) :
    typeAngles c φ y = {ψ : ℝ | Work.Landing.rayAccum c φ ψ = {y}} := rfl

/-- **Closedness of the type of a repelling periodic point.**

The set of angles whose dynamic ray accumulates exactly at the repelling periodic point `y` is
closed in `ℝ`: this is `Work.LandLeaves.isClosed_rayAccum_singleton`, transported along the
definitional equality with `typeAngles` (which is the same set, cf. `typeAngles_eq_setOf`). -/
theorem isClosed_typeAngles {c : ℂ} {φ : ℂ → ℂ} {k : ℕ} {y : ℂ}
    (hφ : Work.ParamRays.IsDynBottcher c φ) (hrep : Work.Landing.IsRepelling c k y) :
    IsClosed (Work.LandLeaves.typeAngles c φ y) := by
  rw [typeAngles_eq_setOf]
  exact isClosed_rayAccum_singleton hφ hrep

end Work.LandLeaves
