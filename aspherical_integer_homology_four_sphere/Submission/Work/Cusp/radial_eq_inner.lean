import Mathlib
import Submission.Work.Cusp.Basic

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.Cusp

/-- In the inner region `‖p‖∞ ≤ 1/2` the metric radial coordinate is the linear function
`r = 2 r_J ‖p‖∞` of the layer parameter. -/
theorem radial_eq_inner (v : Fin 5) (p y : E2) (hp : nrm p ≤ 1/2) :
    radial v p y = 2 * rJ * nrm p := by
  rw [radial, ite_eq_left hp]

end Work.Cusp
