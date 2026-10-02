import Submission.Work.Kunneth.lerayHirschFull_trivial

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The Leray–Hirsch input of area WHITNEY

`Work.LerayHirsch.kunnethCP_of_trivialBundles` reduces the single input of the Leray–Hirsch
induction, `Work.LerayHirsch.KunnethCP`, to the trivial-bundle statement
`Work.Kunneth.lerayHirschFull_trivial`.  This file records the resulting bridge: **KünnethCP is
proved**, hence `Work.LerayHirsch.lerayHirschFull_of_kunnethCP` and the consumers built on it
(`Work.LerayHirsch.LerayHirsch`, `Work.LerayHirsch.CohMap_projMap_injective_of_LerayHirsch`, the
Whitney sum formula and, through it, the areas GEN and THOM) are no longer conditional on it.
-/

namespace Work.Kunneth

theorem kunnethCP : Work.LerayHirsch.KunnethCP :=
  Work.LerayHirsch.kunnethCP_of_trivialBundles lerayHirschFull_trivial

end Work.Kunneth
