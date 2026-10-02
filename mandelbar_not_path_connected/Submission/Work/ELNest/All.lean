/-
# ELNest — the whole area

Import this module to get everything the area `Submission/Work/ELNest/` delivers; see `NOTES.md`
for the statements, the provenance of the hypotheses, and the map to the structures
`Work.ELRig.Z1Nest` / `Work.ELRig.B2Data` that consume this area.

`Audit.lean` records `#print axioms` for every main theorem: they depend only on
`propext`, `Classical.choice` and `Quot.sound` (no `sorryAx`).
-/
import Submission.Work.ELNest.Defs
import Submission.Work.ELNest.Flower
import Submission.Work.ELNest.Setup
import Submission.Work.ELNest.Side
import Submission.Work.ELNest.bAng_range
import Submission.Work.ELNest.bAng_nest_arc
import Submission.Work.ELNest.T_iterate_bAng
import Submission.Work.ELNest.Qlev_facts
import Submission.Work.ELNest.Qp_shift
import Submission.Work.ELNest.Exists
import Submission.Work.ELNest.Chain
import Submission.Work.ELNest.uPair_lands
import Submission.Work.ELNest.uuPair_lands
import Submission.Work.ELNest.armPair_lands
import Submission.Work.ELNest.nestChain_lands
import Submission.Work.ELNest.nestPair_nest
import Submission.Work.ELNest.Nest_coLand
import Submission.Work.ELNest.g_eq_localInverse
import Submission.Work.ELNest.tendsto_iterate_g
import Submission.Work.ELNest.Qshift_image
import Submission.Work.ELNest.Qnest_shrinks
import Submission.Work.ELNest.Dnest_shrinks_aux
import Submission.Work.ELNest.Dnest_shrinks
import Submission.Work.ELNest.Dnest_limit
import Submission.Work.ELNest.Dnest
import Submission.Work.ELNest.ArmChain
import Submission.Work.ELNest.armChain_lands
import Submission.Work.ELNest.armChain_nest
import Submission.Work.ELNest.armChainA_norm
import Submission.Work.ELNest.armChainB_norm
import Submission.Work.ELNest.armChainC_norm
import Submission.Work.ELNest.Arm_coLand
import Submission.Work.ELNest.b2_fix_of_lands
import Submission.Work.ELNest.Dshift_image
import Submission.Work.ELNest.isOpen_D
import Submission.Work.ELNest.cut_mem_A
import Submission.Work.ELNest.cut_unique_A
import Submission.Work.ELNest.z1_mem_armA
import Submission.Work.ELNest.z0_notMem_clA
import Submission.Work.ELNest.arms_basic
import Submission.Work.ELNest.rot_cut
import Submission.Work.ELNest.Facts
import Submission.Work.ELNest.T10_armA1
import Submission.Work.ELNest.T10_armB1
import Submission.Work.ELNest.T10_armC1

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

