import Submission.Work.SeedCertRay.DataAll

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.SeedCertRay

set_option maxRecDepth 100000

theorem lvl_60 : chkLvl 60 = true := by decide
theorem lvl_61 : chkLvl 61 = true := by decide
theorem lvl_62 : chkLvl 62 = true := by decide
theorem lvl_63 : chkLvl 63 = true := by decide
theorem lvl_64 : chkLvl 64 = true := by decide
theorem lvl_65 : chkLvl 65 = true := by decide
theorem lvl_66 : chkLvl 66 = true := by decide
theorem lvl_67 : chkLvl 67 = true := by decide
theorem lvl_68 : chkLvl 68 = true := by decide
theorem lvl_69 : chkLvl 69 = true := by decide
theorem lvl_70 : chkLvl 70 = true := by decide
theorem lvl_71 : chkLvl 71 = true := by decide
theorem lvl_72 : chkLvl 72 = true := by decide
theorem lvl_73 : chkLvl 73 = true := by decide
theorem lvl_74 : chkLvl 74 = true := by decide
theorem lvl_75 : chkLvl 75 = true := by decide
theorem lvl_76 : chkLvl 76 = true := by decide
theorem lvl_77 : chkLvl 77 = true := by decide
theorem lvl_78 : chkLvl 78 = true := by decide
theorem lvl_79 : chkLvl 79 = true := by decide
theorem lvl_80 : chkLvl 80 = true := by decide
theorem pet_71 : chkPetal 71 = true := by decide
theorem pet_72 : chkPetal 72 = true := by decide
theorem pet_73 : chkPetal 73 = true := by decide
theorem pet_74 : chkPetal 74 = true := by decide
theorem pet_75 : chkPetal 75 = true := by decide
theorem pet_76 : chkPetal 76 = true := by decide
theorem pet_77 : chkPetal 77 = true := by decide
theorem pet_78 : chkPetal 78 = true := by decide
theorem pet_79 : chkPetal 79 = true := by decide
theorem pet_80 : chkPetal 80 = true := by decide

end Work.SeedCertRay
