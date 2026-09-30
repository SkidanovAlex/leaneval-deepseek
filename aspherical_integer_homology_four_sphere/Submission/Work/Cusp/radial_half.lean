import Mathlib
import Submission.Work.Cusp.Basic

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.Cusp

/-- At the junction layer `‖p‖∞ = 1/2` the radial coordinate takes the value `r_J`: the two
branches of `radial` agree there, and the inner branch is `2 r_J ‖p‖∞ = 2·3·(1/2) = 3 = r_J`. -/
theorem radial_half (v : Fin 5) (p y : E2) (hp : nrm p = 1/2) : radial v p y = rJ := by
  simp only [radial, hp, rJ, le_refl, reduceIte]
  norm_num

end Work.Cusp
