/-
# ELRig — the whole area

`import Submission.Work.ELRig.All` brings in the entire equator-curve rigidity: the vocabulary,
the two-sidedness API of the pair curves and the tripod, the inputs from the sibling areas, the
API of the equator, and the main theorem `Work.EL.equatorLeak`.
-/
import Submission.Work.ELRig.Defs
import Submission.Work.ELRig.LocalInverse.exists_analytic_localInverse
import Submission.Work.ELRig.NestCut.exists_cut_mem_of_crosses
import Submission.Work.ELRig.Sides
import Submission.Work.ELRig.Inputs
import Submission.Work.ELRig.Flower
import Submission.Work.ELRig.RayLift
import Submission.Work.ELRig.continuousAt_invOn
import Submission.Work.ELRig.levelParam_spec
import Submission.Work.ELRig.exists_preimage_rayTail
import Submission.Work.ELRig.exists_liftCurvesV2
import Submission.Work.ELRig.exists_liftCurvesV3
import Submission.Work.ELRig.exists_liftSidesV2
import Submission.Work.ELRig.exists_liftSides_of_anti
import Submission.Work.ELRig.Arm
import Submission.Work.ELRig.cert
import Submission.Work.ELRig.rayPt_iterate
import Submission.Work.ELRig.Pa_subset_K
import Submission.Work.ELRig.localInjOn_F
import Submission.Work.ELRig.deriv_ne_zero_of_injOn
import Submission.Work.ELRig.deriv_iterate_ne_zero_of_notMem_orbit
import Submission.Work.ELRig.eqOn_real_of_frequently_real
import Submission.Work.ELRig.rayTail_lift
import Submission.Work.ELRig.equatorTail_mem_near
import Submission.Work.ELRig.reach
import Submission.Work.ELRig.rigidity
import Submission.Work.ELRig.EquatorLeak
import Submission.Work.ELRig.Assembly
import Submission.Work.ELRig.FlowerStrand
import Submission.Work.ELRig.StrandHint
import Submission.Work.ELRig.exists_local_angle_at_lift
import Submission.Work.ELRig.CylSides
import Submission.Work.ELRig.MainCyl
import Submission.Work.ELRig.odd_transversal_level
import Submission.Work.ELRig.exists_analytic_rayCylLift
import Submission.Work.ELRig.exists_pairSideNear_of_crossingOdd
import Submission.Work.ELRig.TailBand
import Submission.Work.ELRig.exists_side_flip
import Submission.Work.ELRig.ParityMain
import Submission.Work.ELRig.ParityEnd
import Submission.Work.ELRig.sidePreserve_core
import Submission.Work.ELRig.sidePreserve_of_rayCylLift
import Submission.Work.ELRig.sidePreserve_core_parity

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

