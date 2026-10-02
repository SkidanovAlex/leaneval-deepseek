import Submission.Work.SeedCertRay.DataAll

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.SeedCertRay

set_option maxRecDepth 100000

theorem lvl_20 : chkLvl 20 = true := by decide
theorem lvl_21 : chkLvl 21 = true := by decide
theorem lvl_22 : chkLvl 22 = true := by decide
theorem lvl_23 : chkLvl 23 = true := by decide
theorem lvl_24 : chkLvl 24 = true := by decide
theorem lvl_25 : chkLvl 25 = true := by decide
theorem lvl_26 : chkLvl 26 = true := by decide
theorem lvl_27 : chkLvl 27 = true := by decide
theorem lvl_28 : chkLvl 28 = true := by decide
theorem lvl_29 : chkLvl 29 = true := by decide
theorem lvl_30 : chkLvl 30 = true := by decide
theorem lvl_31 : chkLvl 31 = true := by decide
theorem lvl_32 : chkLvl 32 = true := by decide
theorem lvl_33 : chkLvl 33 = true := by decide
theorem lvl_34 : chkLvl 34 = true := by decide
theorem lvl_35 : chkLvl 35 = true := by decide
theorem lvl_36 : chkLvl 36 = true := by decide
theorem lvl_37 : chkLvl 37 = true := by decide
theorem lvl_38 : chkLvl 38 = true := by decide
theorem lvl_39 : chkLvl 39 = true := by decide

end Work.SeedCertRay
