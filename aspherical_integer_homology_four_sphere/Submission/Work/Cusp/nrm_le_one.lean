import Mathlib
import Submission.Work.Cusp.Basic

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.Cusp

/-- The sup norm of a point of the square `Sq = [-1,1]²` is at most `1`: immediate from
`nrm p = max |p 0| |p 1|` and the two bounds `|p 0| ≤ 1`, `|p 1| ≤ 1` of membership in `Sq`. -/
theorem nrm_le_one {p : E2} (hp : p ∈ Sq) : nrm p ≤ 1 := by
  exact max_le hp.1 hp.2

end Work.Cusp
