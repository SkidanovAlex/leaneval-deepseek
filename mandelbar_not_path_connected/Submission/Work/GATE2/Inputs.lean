/-
# GATE2 — the sibling-export surface consumed by this area

This module lists (as imports) **exactly** the sibling modules whose exports the GATE2 chapter
consumes: GATE (the delivered gate chapter, minus the still-in-flight bridge
`GATE/Bridge/transitData_of_PARIMPL`), ELRig (the equator rigidity, minus the in-flight
`ELRig/sidePreserve_core`), PARIMPL, NAKANE, FatouCoord, Bottcher, Final, ELNest, ELTop,
ParamRays.  Importing it is equivalent to importing `Submission.Work.GATE.All` and
`Submission.Work.ELRig.All` **except** that it does not depend on the two modules that were
still being written when this file was last edited; see `NOTES.md` §9.
-/
import Submission.Work.ELRig.Arm
import Submission.Work.ELRig.Assembly
import Submission.Work.ELRig.Cyl.continuous_tau
import Submission.Work.ELRig.Cyl.gamma_mem_halfPlane_iff
import Submission.Work.ELRig.CylLift
import Submission.Work.ELRig.CylSides
import Submission.Work.ELRig.Defs
import Submission.Work.ELRig.DerivSign.deriv_sign
import Submission.Work.ELRig.EquatorLeak
import Submission.Work.ELRig.Flower
import Submission.Work.ELRig.FlowerStrand
import Submission.Work.ELRig.Inputs
import Submission.Work.ELRig.LocalInverse.exists_analytic_localInverse
import Submission.Work.ELRig.MainCyl
import Submission.Work.ELRig.Mono.local_mono_norm
import Submission.Work.ELRig.NestCut.exists_cut_mem_of_crosses
import Submission.Work.ELRig.Pa_subset_K
import Submission.Work.ELRig.ParityEnd
import Submission.Work.ELRig.ParityMain
import Submission.Work.ELRig.RayLift
import Submission.Work.ELRig.RayPtC.rayPt_complex_extension
import Submission.Work.ELRig.RootArcBridge
import Submission.Work.ELRig.SideFlipChart
import Submission.Work.ELRig.Sides
import Submission.Work.ELRig.StrandHint
import Submission.Work.ELRig.SublevelInterval.sublevel_interval_of_continuous
import Submission.Work.ELRig.TailBand
import Submission.Work.ELRig.analyticAt_im_invFunOn_rayPt
import Submission.Work.ELRig.analyticOnNhd_dynBottcher
import Submission.Work.ELRig.analyticOnNhd_invFunOn
import Submission.Work.ELRig.analyticOn_rayPt_of_analytic
import Submission.Work.ELRig.analytic_local_crossing
import Submission.Work.ELRig.analytic_local_crossing_v2
import Submission.Work.ELRig.cert
import Submission.Work.ELRig.chart_local_inverse
import Submission.Work.ELRig.chart_local_structure
import Submission.Work.ELRig.chart_sphere_crossings
import Submission.Work.ELRig.chart_sphere_crossings_small
import Submission.Work.ELRig.continuousAt_invOn
import Submission.Work.ELRig.countable_infinite_levels
import Submission.Work.ELRig.countable_level_set_exceptions
import Submission.Work.ELRig.countable_setOf_interval_constant
import Submission.Work.ELRig.countable_zeros_of_analyticOn
import Submission.Work.ELRig.cover_of_crosscut
import Submission.Work.ELRig.crosscut_pair_separation
import Submission.Work.ELRig.crosscut_separation_ball
import Submission.Work.ELRig.crosscut_tools
import Submission.Work.ELRig.crossing_arc_separation
import Submission.Work.ELRig.crossing_of_local_structure
import Submission.Work.ELRig.crossing_separation
import Submission.Work.ELRig.cyl_horizontal_isolated
import Submission.Work.ELRig.deriv_iterate_ne_zero_of_notMem_orbit
import Submission.Work.ELRig.deriv_ne_zero_of_injOn
import Submission.Work.ELRig.eqOn_real_of_frequently_real
import Submission.Work.ELRig.equatorTail_mem_near
import Submission.Work.ELRig.even_sign_changes
import Submission.Work.ELRig.exists_Ioo_notMem_of_countable
import Submission.Work.ELRig.exists_analytic_rayCylLift
import Submission.Work.ELRig.exists_angle_flip
import Submission.Work.ELRig.exists_eta_shifted_notMem_countable
import Submission.Work.ELRig.exists_liftCurvesV2
import Submission.Work.ELRig.exists_liftCurvesV3
import Submission.Work.ELRig.exists_liftSidesV2
import Submission.Work.ELRig.exists_liftSides_of_anti
import Submission.Work.ELRig.exists_localInverseAt_of_psi_eq_b2
import Submission.Work.ELRig.exists_local_angle_at_lift
import Submission.Work.ELRig.exists_pairSideNear_of_crossingOdd
import Submission.Work.ELRig.exists_preimage_rayTail
import Submission.Work.ELRig.exists_rayCylLift
import Submission.Work.ELRig.exists_side_flip
import Submission.Work.ELRig.im_sideFlipChart_eq_zero_iff
import Submission.Work.ELRig.joined_of_arc_one_side
import Submission.Work.ELRig.joined_of_not_crossing
import Submission.Work.ELRig.levelParam_spec
import Submission.Work.ELRig.levelSet_im_finite_generic
import Submission.Work.ELRig.levelSet_im_finite_small
import Submission.Work.ELRig.level_window_shift_bij
import Submission.Work.ELRig.localInjOn_F
import Submission.Work.ELRig.localInverse_sphere_two
import Submission.Work.ELRig.local_arc_portion
import Submission.Work.ELRig.local_arc_portion_of_rays
import Submission.Work.ELRig.local_data_all
import Submission.Work.ELRig.not_joined_of_arc_crossing
import Submission.Work.ELRig.odd_ncard_zeros_iff
import Submission.Work.ELRig.odd_transversal_level
import Submission.Work.ELRig.pointwise_pin
import Submission.Work.ELRig.range_lift_closed
import Submission.Work.ELRig.rayCylLift_far_left_pin
import Submission.Work.ELRig.rayCylLift_range_tau
import Submission.Work.ELRig.rayCylLift_tau_far_bound
import Submission.Work.ELRig.rayPt_deriv_ne_zero
import Submission.Work.ELRig.rayPt_iterate
import Submission.Work.ELRig.rayTail_lift
import Submission.Work.ELRig.reach
import Submission.Work.ELRig.rigidity
import Submission.Work.ELRig.same_side_of_even_flips
import Submission.Work.ELRig.sideFlipChart_crossing
import Submission.Work.ELRig.sideFlipChart_crossing_v2
import Submission.Work.ELRig.sideFlipChart_isOpenMap
import Submission.Work.ELRig.sideFlipChart_open_on_ball
import Submission.Work.ELRig.sideFlip_at_ray
import Submission.Work.ELRig.sideFlip_gamma2_local_angle
import Submission.Work.ELRig.side_flip_at_crossing
import Submission.Work.ELRig.side_flip_at_crossing_gamma2
import Submission.Work.ELRig.side_of_odd_crossings
import Submission.Work.ELRig.sign_flip_of_two_components
import Submission.Work.ELRig.sign_flip_of_two_components_horiz
import Submission.Work.GATE.Defs
import Submission.Work.GATE.Gate.Defs
import Submission.Work.GATE.Gate.Residual
import Submission.Work.GATE.Gate.Transport
import Submission.Work.GATE.Gate.base_at_root
import Submission.Work.GATE.Gate.branchData_alpha1_of_rootParabolic
import Submission.Work.GATE.Integration
import Submission.Work.GATE.Nest.base_window
import Submission.Work.GATE.Nest.deviation_eq_of_mem_paramRay
import Submission.Work.GATE.Nest.exists_nest_level_window
import Submission.Work.GATE.Nest.mem_paramRay_of_notMem_K
import Submission.Work.GATE.Nest.nest_angle_design
import Submission.Work.GATE.Nest.nest_angle_window
import Submission.Work.GATE.Nest.nest_angle_z1
import Submission.Work.GATE.Nest.ray_angle_of_near_sides
import Submission.Work.GATE.Segment.blowup_at_endpoint
import Submission.Work.GATE.Segment.crossing_two_tongues
import Submission.Work.GATE.Segment.exists_segment_near
import Submission.Work.GATE.Segment.exists_two_lattice_hits
import Submission.Work.GATE.Segment.seg_tongues
import Submission.Work.GATE.Segment.seg_tongues_parabolic
import Submission.Work.GATE.TwoSided
import Submission.Work.GATE.TwoSided_of_residual
import Submission.Work.PARIMPL.Basic
import Submission.Work.PARIMPL.Leak
import Submission.Work.PARIMPL.Transit
import Submission.Work.PARIMPL.Match
import Submission.Work.PARIMPL.robust_of_greenOpen
import Submission.Work.NAKANE.GreenJoint
import Submission.Work.NAKANE.BottcherJoint
import Submission.Work.Final.equatorLeak_shift
import Submission.Work.ParamRaysCrit.CritDomain
import Submission.Work.ELNest.T_iterate_bAng
import Submission.Work.ELTop.isOpen_pairSide
import Submission.Work.ELTop.rayPt_inj
import Submission.Work.ELTop.rayPt_add_int

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

