import Mathlib
import Submission.Work.Cusp.Basic
import Submission.Work.Cusp.uPerim_mem
import Submission.Work.Cusp.nrm_bnd

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.Cusp

/-- The perimeter parameter `u p = uPerim (bnd p)` of a nonzero point of the square `Sq` lies in
`[0,1)`: `bnd p` is the radial projection of `p` onto the boundary `∂Sq`, whose sup norm is `1`,
and `uPerim` maps `∂Sq` into `[0,1)` (`uPerim_mem`). -/
theorem u_mem {p : E2} (hp : p ∈ Sq) (h0 : p ≠ 0) : 0 ≤ u p ∧ u p < 1 := by
  rw [u]
  exact uPerim_mem (nrm_bnd h0)

end Work.Cusp
