import Submission.Work.Landing.Land.Main

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# The image of the accumulation set of a dynamic ray (alias)

The ray transfer `T_c '' rayAccum c φ θ = rayAccum c φ (angDouble θ)` is proved in
`Submission/Work/Landing/Land/Main.lean` as `Work.Landing.rayAccum_image`.  This module records the
same statement under the name `Work.Landing.Rays.image_rayAccum`, which the sibling areas use.
-/

namespace Work.Landing.Rays

theorem image_rayAccum {c : ℂ} {φ : ℂ → ℂ} (h : Work.ParamRays.IsDynBottcher c φ) (θ : ℝ) :
    LeanEval.ComplexAnalysis.Tantibar c '' Work.Landing.rayAccum c φ θ =
      Work.Landing.rayAccum c φ ((Work.Landing.angDouble) θ) :=
  Work.Landing.rayAccum_image h θ

end Work.Landing.Rays
