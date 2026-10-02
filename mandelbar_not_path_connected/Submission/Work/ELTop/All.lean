/-
# `Submission.Work.ELTop` — the area in one import

Everything this area delivers: the vocabulary (`Defs`), the plane topology of the ray polygons
(T1–T5), the two-sidedness of pair curves and of the tripod (T6, T8, T7), the bridge to the
landing vocabulary (T9), and the discharge of the ELRig input structures
`Work.EL.PairSides` / `Work.EL.TripodSides`.
-/
import Submission.Work.ELTop.Defs
import Submission.Work.ELTop.rayPt_add_int
import Submission.Work.ELTop.rayPiece_eq_image
import Submission.Work.ELTop.closure_rayPiece
import Submission.Work.ELTop.continuous_rayPt_angle
import Submission.Work.ELTop.rayPt_inj
import Submission.Work.ELTop.paramRay_disjoint
import Submission.Work.ELTop.landsN_mem_K
import Submission.Work.ELTop.landsN_map
import Submission.Work.ELTop.isJordanCurve_range_liftIco
import Submission.Work.ELTop.polyCurve_isJordan
import Submission.Work.ELTop.isClosed_polyCurve
import Submission.Work.ELTop.isOpen_polyRegion
import Submission.Work.ELTop.seed_mem_polyRegion
import Submission.Work.ELTop.polyRegion_eq_bounded_side
import Submission.Work.ELTop.polyRegion_subset_pairSideNear
import Submission.Work.ELTop.polyRegion_subset_pot_lt
import Submission.Work.ELTop.polyRegion_eq_inter_pairSideNear
import Submission.Work.ELTop.polyRegion_eq_iInter_pairSideNear
import Submission.Work.ELTop.arcLen_ne_zero_of_polyAdmissible
import Submission.Work.ELTop.mem_polyRegion_iff_of_notMem_K
import Submission.Work.ELTop.frontier_polyRegion_inter_K
import Submission.Work.ELTop.landing_mem_polyRegion
import Submission.Work.ELTop.simplyConnectedSpace_polyRegion
import Submission.Work.ELTop.pairSides_decomposition
import Submission.Work.ELTop.paramRay_subset_pairSide
import Submission.Work.ELTop.paramRay_subset_pairSideNear
import Submission.Work.ELTop.isClosed_pairCurve
import Submission.Work.ELTop.isOpen_pairSide
import Submission.Work.ELTop.pairSide_subset_pairSide
import Submission.Work.ELTop.pairSide_subset_pairSideNear
import Submission.Work.ELTop.pair_landing_mem_of_preconnected
import Submission.Work.ELTop.tripodArms_disjoint
import Submission.Work.ELTop.tripodArms_cover
import Submission.Work.ELTop.landsN_iff_landsAt
import Submission.Work.ELTop.RegionBasics
import Submission.Work.ELTop.RigInput
import Submission.Work.ELTop.RigTripod

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

