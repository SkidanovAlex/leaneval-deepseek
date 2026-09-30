/-
# `RiemLib/AxiomCheck.lean` — axiom audit of the vendored library

The deliverable for area RL asks for a confirmation, by `#print axioms`, that the key theorems of the
vendored library are axiom-clean: they must depend only on `propext`, `Quot.sound` and
`Classical.choice` (the permitted axioms of `config.json`), and in particular must not depend on
`sorryAx`.  Building this module prints the axioms of every declaration listed below; the expected
output is, for each of them, exactly

    'X' depends on axioms: [propext, Classical.choice, Quot.sound]

(Lean prints the axioms actually used; `propext` and `Quot.sound` may be absent for purely
computational declarations.)

The list covers the six key theorems named in the blueprint (the XuLift / GExp covering pieces, the
locally-injective form of the conjugate-radius bound, Hopf–Rinow, Rauch's `π/√K`, the local
injectivity of `GExp`), the injectivity-radius structure, and the whole Klingenberg long-homotopy
lifting kit, plus the two interface lemmas of `RiemLib/API.lean` and the library's own top theorem
`Submission.Klingenberg.sphere_theorem_of_klingenberg` as a smoke test.
-/

import Submission.Work.RiemLib.API
import Submission.Work.RiemLib.SecNonpos.All
import Submission.Work.RiemLib.Klingenberg

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false


#print axioms Submission.XuLift.gexpMap
#print axioms Submission.XuLift.contMDiffOn_GExp_model
#print axioms Submission.XuLift.isLocalDiffeomorphAt_GExp
#print axioms Submission.XuLift.exists_pos_ball_lift_GExp
#print axioms Submission.GExpLocalInj.locallyInjectiveAtGExp_of_lt_pi_div_sqrt
#print axioms Submission.RayConj.pi_div_sqrt_le_of_singular_mfderiv
#print axioms Submission.RayConj.locallyInjectiveAtGExp_of_norm_lt_pi_div_sqrt
#print axioms Submission.ConjCut.isInvertible_mfderiv_GExp_of_norm_lt_pi_div_sqrt
#print axioms Submission.SingularConj.singular_imp_conjTime
#print axioms Submission.RauchK.eqOn_zero_of_jacobi_of_curvLe
#print axioms Submission.RauchK.pi_div_sqrt_le_of_isConjugateTime
#print axioms Submission.ChartCurv.curvVec_eq_chart
#print axioms Submission.HopfRinow.exists_geodesic_riemannianEDist_eq
#print axioms Submission.HopfRinow.riemannianEDist_GExp_ray_le
#print axioms Submission.InjRadius.exists_unique_GExp_of_injAtLeast
#print axioms Submission.InjRadius.edist_GExp_eq_norm_of_injAtLeast
#print axioms Submission.InjRadius.two_mul_le_of_injAllAtLeast_of_geodCurve_loop
#print axioms Work.OddBound.longHomotopy.exists_lift_of_short
#print axioms Work.OddBound.longHomotopy.exists_lift_of_short_bis
#print axioms Work.OddBound.longHomotopy.lift_family_of_short
#print axioms Work.OddBound.longHomotopy.continuousOn_lift_family_of_short
#print axioms Work.OddBound.longHomotopy.lift_family_continuity_core
#print axioms Work.OddBound.longHomotopy.exists_tendsto_of_lift
#print axioms Work.OddBound.longHomotopy.gauss_pairing_fibre
#print axioms Work.RiemLib.CurvLe_of_nonpos
#print axioms Work.RiemLib.CurvLe_zero_iff
#print axioms Work.RiemLib.exists_lt_pi_div_sqrt
#print axioms Work.RiemLib.isInvertible_mfderiv_gexpMap_of_norm_lt_pi_div_sqrt
#print axioms Work.RiemLib.exists_pos_ball_lift_gexpMap_of_norm_lt_pi_div_sqrt
#print axioms Work.RiemLib.exists_gexpMap_eq
#print axioms Work.RiemLib.SecNonpos.exists_lift_of_short_of_nonpos
#print axioms Work.RiemLib.SecNonpos.lift_family_of_short_of_nonpos
#print axioms Submission.Klingenberg.sphere_theorem_of_klingenberg
