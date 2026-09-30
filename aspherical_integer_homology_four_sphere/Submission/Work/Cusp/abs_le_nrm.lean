import Mathlib
import Submission.Work.Cusp.Basic

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.Cusp

/-- Each coordinate of a point of `E2` is bounded by the sup norm `nrm p = max |p 0| |p 1|`. -/
theorem abs_le_nrm_aux (p : E2) : |p 0| ≤ nrm p ∧ |p 1| ≤ nrm p := by
  constructor <;> simp [nrm]

theorem abs_le_nrm (p : E2) (i : Fin 2) : |p i| ≤ nrm p := by
  fin_cases i <;> simp [nrm]

end Work.Cusp
