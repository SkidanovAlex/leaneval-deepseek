import Mathlib
import Submission.Work.HypModel.Basic
import Submission.Work.HypModel.hasFDerivAt_hypOfUHS
import Submission.Work.HypModel.lorentz_dHypOfUHS

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.HypModel

/-- The Lorentz form pulled back by the upper half space chart `hypOfUHS` is the hyperbolic
metric `uhsMetric q v w = (q 3)⁻²⟪v,w⟫` of the upper half space model.  This follows from the
explicit derivative `hasFDerivAt_hypOfUHS` and the computation `lorentz_dHypOfUHS`. -/
theorem uhs_pullback {q : E4} (hq : q 3 ≠ 0) (v w : E4) :
    uhsMetric q v w = lorentz (fderiv ℝ hypOfUHS q v) (fderiv ℝ hypOfUHS q w) := by
  rw [(hasFDerivAt_hypOfUHS hq).fderiv]
  exact (lorentz_dHypOfUHS hq v w).symm

end Work.HypModel
