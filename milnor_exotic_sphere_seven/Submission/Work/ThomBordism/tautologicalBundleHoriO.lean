import Mathlib
import Submission.Work.ThomBordism.Grassmann.Oriented
import Submission.Work.ThomBordism.coorientationRef

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option maxHeartbeats 800000

/-!
# The tautological bundle satisfies the orientation hypothesis of the canonical Thom class

`Work.Thom.realThomClassOf hn Z hori` (the *canonical*, chart-constructed Thom class of an oriented
real bundle) requires `hori : ∀ i j x, 0 < det (Z.coordChange i j x)`.  For the tautological oriented
bundle `Work.ThomBordism.Grassmann.tautologicalBundle k 10 = tautologicalBundleO k 10` this is by
construction: its transition functions are the corrected `coordChangeO`, whose determinants are
positive (`Work.ThomBordism.Grassmann.det_coordChangeO_pos`).

This file is `sorry`-free and exists so that consumers of
`Work.Thom.realThomClassOf hk (tautologicalBundle k 10) horiO` — e.g. the signed canonical
local-degree statements — can obtain `horiO` without importing a module that contains a `sorry`.
-/

namespace Work.ThomBordism

/-- **The tautological bundle satisfies the orientation hypothesis of `Work.Thom.realThomClassOf`.** -/
theorem tautologicalBundle_horiO (k : ℕ) :
    ∀ (i j : Work.ThomBordism.Grassmann.ChartIdx k 10)
      (x : ↥((Work.ThomBordism.Grassmann.tautologicalBundle k 10).baseSet i
        ∩ (Work.ThomBordism.Grassmann.tautologicalBundle k 10).baseSet j)),
      0 < LinearMap.det (((Work.ThomBordism.Grassmann.tautologicalBundle k 10).coordChange i j
        (x : Work.ThomBordism.Grassmann.OG k 10)).toLinearMap) :=
  fun i j x => Work.ThomBordism.Grassmann.det_coordChangeO_pos i j x.1 x.2

end Work.ThomBordism
