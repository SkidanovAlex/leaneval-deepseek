import Mathlib
import Submission.Work.Cusp.Basic

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.Cusp

/-- A point of the square of sup norm `1` already lies on the boundary `∂Sq`, so the radial
projection `bnd p = (nrm p)⁻¹ • p` fixes it: at `nrm q = 1` we have `(nrm q)⁻¹ = 1` and
`1 • q = q`. -/
theorem bnd_eq_self {q : E2} (h1 : nrm q = 1) : bnd q = q := by
  simp [bnd, h1]

end Work.Cusp
