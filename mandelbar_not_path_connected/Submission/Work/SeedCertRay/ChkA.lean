import Submission.Work.SeedCertRay.DataAll

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.SeedCertRay

set_option maxRecDepth 100000

theorem lvl_0 : chkLvl 0 = true := by decide
theorem lvl_1 : chkLvl 1 = true := by decide
theorem lvl_2 : chkLvl 2 = true := by decide
theorem lvl_3 : chkLvl 3 = true := by decide
theorem lvl_4 : chkLvl 4 = true := by decide
theorem lvl_5 : chkLvl 5 = true := by decide
theorem lvl_6 : chkLvl 6 = true := by decide
theorem lvl_7 : chkLvl 7 = true := by decide
theorem lvl_8 : chkLvl 8 = true := by decide
theorem lvl_9 : chkLvl 9 = true := by decide
theorem lvl_10 : chkLvl 10 = true := by decide
theorem lvl_11 : chkLvl 11 = true := by decide
theorem lvl_12 : chkLvl 12 = true := by decide
theorem lvl_13 : chkLvl 13 = true := by decide
theorem lvl_14 : chkLvl 14 = true := by decide
theorem lvl_15 : chkLvl 15 = true := by decide
theorem lvl_16 : chkLvl 16 = true := by decide
theorem lvl_17 : chkLvl 17 = true := by decide
theorem lvl_18 : chkLvl 18 = true := by decide
theorem lvl_19 : chkLvl 19 = true := by decide

end Work.SeedCertRay
