import Submission.Work.SeedCertRay.DataAll

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.SeedCertRay

set_option maxRecDepth 100000

theorem lvl_40 : chkLvl 40 = true := by decide
theorem lvl_41 : chkLvl 41 = true := by decide
theorem lvl_42 : chkLvl 42 = true := by decide
theorem lvl_43 : chkLvl 43 = true := by decide
theorem lvl_44 : chkLvl 44 = true := by decide
theorem lvl_45 : chkLvl 45 = true := by decide
theorem lvl_46 : chkLvl 46 = true := by decide
theorem lvl_47 : chkLvl 47 = true := by decide
theorem lvl_48 : chkLvl 48 = true := by decide
theorem lvl_49 : chkLvl 49 = true := by decide
theorem lvl_50 : chkLvl 50 = true := by decide
theorem lvl_51 : chkLvl 51 = true := by decide
theorem lvl_52 : chkLvl 52 = true := by decide
theorem lvl_53 : chkLvl 53 = true := by decide
theorem lvl_54 : chkLvl 54 = true := by decide
theorem lvl_55 : chkLvl 55 = true := by decide
theorem lvl_56 : chkLvl 56 = true := by decide
theorem lvl_57 : chkLvl 57 = true := by decide
theorem lvl_58 : chkLvl 58 = true := by decide
theorem lvl_59 : chkLvl 59 = true := by decide

end Work.SeedCertRay
