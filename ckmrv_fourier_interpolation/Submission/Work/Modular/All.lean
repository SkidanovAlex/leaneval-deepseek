import Submission.Work.Modular.Basic
import Submission.Work.Modular.D_E2_tendsto_atImInfty
import Submission.Work.Modular.E2_S_smul
import Submission.Work.Modular.E2_T_smul
import Submission.Work.Modular.E2_qExpansion_coeff
import Submission.Work.Modular.E2_tendsto_atImInfty
import Submission.Work.Modular.E4_qExpansion_coeff
import Submission.Work.Modular.E4_tendsto_atImInfty
import Submission.Work.Modular.E6_qExpansion_coeff
import Submission.Work.Modular.E8ThetaAux
import Submission.Work.Modular.E8_eight_dvd_sum_sq
import Submission.Work.Modular.E8_sq_norm_even
import Submission.Work.Modular.EisensteinDelta
import Submission.Work.Modular.GroupAlgebra
import Submission.Work.Modular.I_pow_div_two
import Submission.Work.Modular.Lattice
import Submission.Work.Modular.PSLTransfer
import Submission.Work.Modular.Th2_S_smul
import Submission.Work.Modular.Th4_S_smul
import Submission.Work.Modular.ThetaCharDefs
import Submission.Work.Modular.ThetaFuncs
import Submission.Work.Modular.ThetaImagAxis
import Submission.Work.Modular.basisElem_mul_sR
import Submission.Work.Modular.basisElem_mul_tR
import Submission.Work.Modular.eq_of_eqOn_imagPoint
import Submission.Work.Modular.exists_functional_T
import Submission.Work.Modular.finrank_quotient_PSL
import Submission.Work.Modular.gaussSum_inv_of_functionalEquation
import Submission.Work.Modular.imagPoint_S_smul
import Submission.Work.Modular.intervalIntegral_exp_int_mul_two_pi_I
import Submission.Work.Modular.isBoundedAtImInfty_normalizedDerivOfComplex
import Submission.Work.Modular.isModularFormOfWeight_E4
import Submission.Work.Modular.isModularFormOfWeight_E6
import Submission.Work.Modular.isModularFormOfWeight_iff
import Submission.Work.Modular.isQuasiModularFormDepth_mono
import Submission.Work.Modular.isQuasiModularFormDepth_mul
import Submission.Work.Modular.isQuasiModularForm_E2
import Submission.Work.Modular.isQuasiModularForm_iff
import Submission.Work.Modular.mdifferentiable_S_smul
import Submission.Work.Modular.mem_quasiModularSpace
import Submission.Work.Modular.modularForm_of_slash_invariant
import Submission.Work.Modular.mul_basisElem_sub_mem_idealI
import Submission.Work.Modular.poissonSummation_lattice
import Submission.Work.Modular.presentedGroup_equiv_PSL
import Submission.Work.Modular.qExpansion_normalizedDerivOfComplex
import Submission.Work.Modular.quotient_basis
import Submission.Work.Modular.quotient_basis_PSL
import Submission.Work.Modular.quotient_linearIndependent
import Submission.Work.Modular.quotient_spanning
import Submission.Work.Modular.ramanujan_E2
import Submission.Work.Modular.ramanujan_E4
import Submission.Work.Modular.ramanujan_E6
import Submission.Work.Modular.sigmaAlg_basisElem_row
import Submission.Work.Modular.sigmaAlg_idealI_row
import Submission.Work.Modular.slash_defect
import Submission.Work.Modular.slash_sum_E2_pow
import Submission.Work.Modular.theta2_S_smul
import Submission.Work.Modular.theta2_at_cusp
import Submission.Work.Modular.theta4_S_smul
import Submission.Work.Modular.thetaSeries_E8_S_smul
import Submission.Work.Modular.thetaSeries_E8_T_smul
import Submission.Work.Modular.thetaSeries_E8_decomposition
import Submission.Work.Modular.thetaSeries_E8_eq_E4
import Submission.Work.Modular.thetaSeries_E8_summable
import Submission.Work.Modular.thetaSeries_S_smul_of_gaussian
import Submission.Work.Modular.thetaSeries_T_smul
import Submission.Work.Modular.thetaSeries_atImInfty
import Submission.Work.Modular.thetaSeries_decomposition
import Submission.Work.Modular.thetaSeries_imagPoint
import Submission.Work.Modular.thetaSeries_mdifferentiable
import Submission.Work.Modular.thetaSeries_qExpansion_coeff_one
import Submission.Work.Modular.thetaSeries_rank24
import Submission.Work.Modular.thetaSeries_summable
import Submission.Work.Modular.weight12_eq_E12_sub_discriminant

/-!
# The quasimodular-forms / lattice-theta-series chapter of the CKMRV project

Single import point for everything proved in `Submission/Work/Modular/`.

* `Submission.Work.Modular.Basic`: quasimodular forms (`IsQuasiModularFormDepth`,
  `IsQuasiModularForm`, `IsModularFormOfWeight`, `quasiModularSpace`, `E2`, `E4`, `E6`).
* `Submission.Work.Modular.Lattice`: lattices, their theta series, the `E8` lattice, the dual
  lattice, and the covolume.
* `Submission.Work.Modular.GroupAlgebra`: the abstract group `Γ = ⟨S, T | S² = (ST)³ = 1⟩`,
  its group algebra, the ideal `I`, the six elements `1, T, TS, S, ST, STS`, and the
  six-dimensional representation `σ`.
* `Submission.Work.Modular.PSLTransfer`: the same objects for `ℂ[PSL(2, ℤ)]`.
-/

