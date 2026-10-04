/-
# Layer A: aggregator / smoke test

Imports (and re-exports) every *proved* module of the STE torus toolkit, so that
`lake build Submission.Work.Diff.STE.LayerA` checks that the whole Layer A library is
mutually consistent (in particular that no two modules declare the same name —
a recurring trap, see DESIGN.md).  Modules that still carry a `sorry` are deliberately
NOT imported here; add them when they are proved.
-/
import Submission.Work.Diff.STE.Torus
import Submission.Work.Diff.STE.integral_fourierExp
import Submission.Work.Diff.STE.fourierCoeff_pd
import Submission.Work.Diff.STE.fourierCoeff_pdVec
import Submission.Work.Diff.STE.wt_pow_le
import Submission.Work.Diff.STE.summable_wt_zpow
import Submission.Work.Diff.STE.l1_le_sqrt_CSq
import Submission.Work.Diff.STE.conv_l2_sq_le
import Submission.Work.Diff.STE.CSq_interpolation
import Submission.Work.Diff.STE.CSq_tail_le
import Submission.Work.Diff.STE.wt_pow_le_monomialSum
import Submission.Work.Diff.STE.monomialSum_le_wt_pow
import Submission.Work.Diff.STE.contDiff_seriesFun
import Submission.Work.Diff.STE.pd_seriesFun
import Submission.Work.Diff.STE.seriesFun_mul
import Submission.Work.Diff.STE.norm_seriesFun_le
import Submission.Work.Diff.STE.integral_seriesFun_mul_conj
import Submission.Work.Diff.STE.trigPoly_dense_L2
import Submission.Work.Diff.STE.CSq_trunc_le
import Submission.Work.Diff.STE.CSq_trunc_sub_le
import Submission.Work.Diff.STE.integral_mul_pd_eq_neg
import Submission.Work.Diff.STE.garding_estimate
import Submission.Work.Diff.STE.commutator_estimate
import Submission.Work.Diff.STE.ENormSq_seriesFun_le
import Submission.Work.Diff.STE.CSq_le_ENormSq_seriesFun
import Submission.Work.Diff.STE.CSq_le_ENormSq
import Submission.Work.Diff.STE.pdVec_contDiff_periodic
import Submission.Work.Diff.STE.ENormSq_succ_eq
import Submission.Work.Diff.STE.friedrichs_commutator
import Submission.Work.Diff.STE.trigPoly_bridge
import Submission.Work.Diff.STE.Energy_basic
import Submission.Work.Diff.STE.CSq_conv_le
import Submission.Work.Diff.STE.CSq_conv_tame_le
import Submission.Work.Diff.STE.CSq_comp_le
import Submission.Work.Diff.STE.finite_bounded_lattice
import Submission.Work.Diff.STE.eq_zero_of_fourierCoeff_eq_zero
import Submission.Work.Diff.STE.summable_weighted_fourierCoeff_of_contDiff
import Submission.Work.Diff.STE.bessel_fourierCoeff
import Submission.Work.Diff.STE.pd_trigFun
import Submission.Work.Diff.STE.hasDerivAt_seriesFun
import Submission.Work.Diff.STE.hasDerivAt_integral_normSq_seriesFun
import Submission.Work.Diff.STE.integral_normSq_seriesFun
import Submission.Work.Diff.STE.garding_estimate_vec
import Submission.Work.Diff.STE.exists_trunc_support
import Submission.Work.Diff.STE.gronwall_linear_bound
import Submission.Work.Diff.STE.ENormSq_pairing_le
import Submission.Work.Diff.STE.energy_le_of_coeff_bounds
import Submission.Work.Diff.STE.periodization_contDiff_periodic
import Submission.Work.Diff.STE.pd_periodization
import Submission.Work.Diff.STE.CSq_comp_vecarg_le
import Submission.Work.Diff.STE.fourierCoeff_mul_seriesFun
import Submission.Work.Diff.STE.exists_finite_chart_cover
import Submission.Work.Diff.STE.ChartComp
import Submission.Work.Diff.STE.exists_norm_bound_finBasis
import Submission.Work.Diff.STE.SNorm
import Submission.Work.Diff.STE.contDiffOn_chartComp
import Submission.Work.Diff.STE.CSq_periodization_le_of_sup_bound
import Submission.Work.Diff.STE.exists_chart_ball_cover
import Submission.Work.Diff.STE.exists_smoothPartition_ball_cover
import Submission.Work.Diff.STE.contDiffOn_locComp
import Submission.Work.Diff.STE.support_locComp_subset
import Submission.Work.Diff.STE.pd_periodization
import Submission.Work.Diff.STE.Energy_basic
import Submission.Work.Diff.STE.contDiff_perComp_of_bump
import Submission.Work.Diff.STE.DeTurckJet
import Submission.Work.Diff.STE.FlatPDE
import Submission.Work.Diff.STE.deTurck.contDiffOn_pPhi
import Submission.Work.Diff.STE.deTurck.pPhi_decomp
import Submission.Work.Diff.STE.deTurck.posDef_gmat
import Submission.Work.Diff.STE.DeTurckField
import Submission.Work.Diff.STE.deTurck.traceVec_eq_sum_invGram
import Submission.Work.Diff.STE.DeTurckCanon

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
