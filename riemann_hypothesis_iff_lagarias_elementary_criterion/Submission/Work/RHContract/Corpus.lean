import Submission.Work.RHContract.Defs
import Submission.Work.RHContract.MarginDefs
import Submission.Work.RHContract.LandauDefs
-- Mertens / Chebyshev
import Submission.Commons.NumberTheory.Mertens.sum_log_prime_ratio_real_tendsto
import Submission.Commons.NumberTheory.Mertens.mertens_log_ratio_rh_bound
import Submission.Commons.NumberTheory.Chebyshev.psi_sub_theta_le_three_sqrt
import Submission.Commons.NumberTheory.Chebyshev.theta_lower_ninetenths
import Submission.Commons.NumberTheory.Chebyshev.theta_upper_11056
import Submission.Commons.NumberTheory.Chebyshev.theta_le_log3_mul
import Submission.Commons.NumberTheory.Chebyshev.sum_prime_inv_sq_abel
import Submission.Commons.NumberTheory.Chebyshev.sum_prime_inv_sq_lower_bound
-- Zeta: the integrated explicit formula (the "farLeft" side of the corpus) and the
-- neutral zero-sum bounds
import Submission.Commons.NumberTheory.Zeta.psiIntegral_tilted_explicit
import Submission.Commons.NumberTheory.Zeta.zeroSum_finset_le_beta
import Submission.Commons.NumberTheory.Zeta.zeroSum_finsum_le_beta
import Submission.Commons.NumberTheory.Zeta.psiBeta_nonneg_of_rh
import Submission.Commons.NumberTheory.Zeta.psi_sub_id_powLog_real
import Submission.Commons.NumberTheory.Zeta.logDeriv_zeta_eq_mellin_psi_sub_id
import Submission.Commons.NumberTheory.Zeta.zeta_eq_emN
import Submission.Commons.NumberTheory.Zeta.zeta_eq_emN_re_gt_one
import Submission.Commons.NumberTheory.Zeta.zeta1_logDeriv_pole_removal
import Submission.Commons.NumberTheory.Zeta.isPreconnected_re_gt_sdiff
import Submission.Commons.NumberTheory.Zeta.not_psi_sub_self_bigO_of_zeta_zero
import Submission.Commons.NumberTheory.Zeta.riemannZeta_eq_zero_iff_trivial_of_re_nonpos
import Submission.Commons.NumberTheory.Zeta.trivial_zero_of_riemannZeta_eq_zero_of_re_nonpos
import Submission.Commons.NumberTheory.Zeta.mem_strip_of_riemannZeta_eq_zero_of_not_trivial
import Submission.Commons.NumberTheory.Zeta.summable_vonMangoldt_mul_rpow
import Submission.Commons.NumberTheory.Zeta.zeta1_ne_zero_re_neg_three_halves_le_zero
-- Robin: the CA parametrisation and its threshold API
import Submission.Commons.NumberTheory.Robin.caMu_ge_iff_caF
import Submission.Commons.NumberTheory.Robin.caMu_pos
import Submission.Commons.NumberTheory.Robin.caSupp_eq_primesLE_xi
import Submission.Commons.NumberTheory.Robin.caSupp_down_closed
import Submission.Commons.NumberTheory.Robin.caU_decomp
import Submission.Commons.NumberTheory.Robin.caMertensSum_eq_logRatioSum_xi
import Submission.Commons.NumberTheory.Robin.caLogN_eq_sum_theta
import Submission.Commons.NumberTheory.Robin.caExp_ge_k_iff_le_xiK
import Submission.Commons.NumberTheory.Robin.caExp_anti_p
import Submission.Commons.NumberTheory.Robin.caXiK_bounds
import Submission.Commons.NumberTheory.Robin.ca_level_two_upper
import Submission.Commons.NumberTheory.Robin.ca_level_two_lower
import Submission.Commons.NumberTheory.Robin.caXi2_lower
import Submission.Commons.NumberTheory.Robin.caXi2_upper
import Submission.Commons.NumberTheory.Robin.caXi_prime
import Submission.Commons.NumberTheory.Robin.ca_55440_in_family
import Submission.Commons.NumberTheory.Robin.sigma_ratio_prime_power_prod
import Submission.Commons.NumberTheory.Robin.caCorrSum_nonpos
import Submission.Commons.NumberTheory.Robin.caCorrSum_ge_inv_sqrt_log
import Submission.Commons.NumberTheory.Robin.caF1_lt_inv_mul_log
import Submission.Commons.NumberTheory.Robin.caF1_le_inv_mul_log
import Submission.Commons.NumberTheory.Robin.robin_caFval_small
import Submission.Commons.NumberTheory.Robin.robin_upper_le_55440
import Submission.Commons.NumberTheory.Robin.robin_of_ca_cover_clean
import Submission.Commons.NumberTheory.Robin.robin_upper_of_large
import Submission.Commons.NumberTheory.Robin.not_rh_exists_nontrivial_zero_gt_half
-- Analysis helpers
import Submission.Commons.Analysis.Real.log_one_add_inv_div_log_strictAntiOn

/-!
# `Work.RHContract.Corpus` — import hub for the RHContract area

Importing this single module makes available

* the definitions of this area (`Work.RHContract.Defs`, `MarginDefs`, `LandauDefs`);
* the Mertens / Chebyshev corpus (`logRatioSum`, `sum_log_prime_ratio_real_tendsto`,
  `psi_sub_theta_le_three_sqrt`, `theta_lower_ninetenths`, `theta_upper_11056`, …);
* the Zeta corpus for the integrated explicit formula and the Mellin transform
  (`psiIntegral_tilted_explicit`, `zeroSum_finset_le_beta`, `zeroSum_finsum_le_beta`,
  `psiBeta_nonneg_of_rh`, `logDeriv_zeta_eq_mellin_psi_sub_id`, `zeta_eq_emN`,
  `zeta1_logDeriv_pole_removal`, `isPreconnected_re_gt_sdiff`, …);
* the Robin corpus for the colossally abundant parametrisation
  (`caMu_ge_iff_caF`, `caSupp_eq_primesLE_xi`, `caU_decomp`,
  `caMertensSum_eq_logRatioSum_xi`, `caLogN_eq_sum_theta`, `caXiK_bounds`,
  `ca_level_two_upper`, `robin_caFval_small`, …).

## IMPORTANT: the corpus splits into two mutually incompatible halves

The corpus modules `Submission.Commons.NumberTheory.Zeta.rectInt_model_multi_pole` and
`Submission.Commons.NumberTheory.Zeta.chebyshevPsi_at_height_farLeft_neg` **both declare**
`Commons.NumberTheory.Zeta.rectInt_model_multi_pole`, so they can never be imported into the
same file (in either order).  Consequently the Zeta corpus has two disjoint halves:

* the **farLeft** half (`chebyshevPsi_at_height_farLeft_neg`, `psiIntegral_tilted_explicit`,
  `psi_integral_lower_bound_explicit`, `zeta1_zero_tilted_term_le`, …) — this hub;
* the **rectInt** half (`rectInt_model_multi_pole`, `rectInt_psiIntF_engineSum`,
  `zeta1Order_sum_le_psiBeta`, `tiltedZeroSum_finset_rh_bound`, `summable_tiltedZeroSum`,
  `zeta1Order_neg_two_mul_nat_add_one`, `zeta1Order_ge_one`, `zetaZeroBall`, …).

The zero-sum bound `‖Σ_ρ m_ρ x^ρ/(ρ(ρ+1))‖ ≤ (2+γ−log 4π)√x` needed by A1/A2 is available
on the **farLeft** side through the neutral modules `zeroSum_finset_le_beta` /
`zeroSum_finsum_le_beta` (which bound `Σ_ρ m_ρ/‖ρ‖²` directly).  Do **not** try to import
`tiltedZeroSum_finset_rh_bound` here; use `zeroSum_finset_le_beta` instead.
-/
