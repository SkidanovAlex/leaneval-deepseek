import Mathlib
import Submission.Work.Cusp.Basic
import Submission.Work.Cusp.Charts
import Submission.Work.Cusp.nrm_continuous

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.Cusp

/-- The superlevel set `{p : E2 | c < nrm p}` of the layer parameter is open: it is the preimage
under the continuous map `nrm` (`nrm_continuous`) of the open halfline `(c, ∞)`. -/
theorem isOpen_nrm_gt (c : ℝ) : IsOpen {p : E2 | c < nrm p} :=
  isOpen_Ioi.preimage nrm_continuous

end Work.Cusp
