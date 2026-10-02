/-
# TripodCert — the radius and containment checks of the uniqueness disc (generated)
-/
import Mathlib
import Submission.Work.TripodCert.Num2
import Submission.Work.TripodCert.Data

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.TripodCert

open Work.SeedCertRay

/-- The periodic boxes of angle class `0` have radius at most `URm`. -/
theorem chkRad_0 : radLeT URm perT 0 = true := by decide

/-- The periodic boxes of angle class `2` have radius at most `URm`. -/
theorem chkRad_2 : radLeT URm perT 2 = true := by decide

/-- The periodic boxes of angle class `0` have radius at most `URmU`. -/
theorem chkRadU_0 : radLeT URmU perT 0 = true := by decide

/-- The periodic boxes of angle class `2` have radius at most `URmU`. -/
theorem chkRadU_2 : radLeT URmU perT 2 = true := by decide

/-- The periodic boxes of angle class `0` lie in the uniqueness disc. -/
theorem chkUBallU_0 : chkUBall Uzx Uzy URmU perT 0 = true := by decide

/-- The periodic boxes of angle class `2` lie in the uniqueness disc. -/
theorem chkUBallU_2 : chkUBall Uzx Uzy URmU perT 2 = true := by decide

end Work.TripodCert
