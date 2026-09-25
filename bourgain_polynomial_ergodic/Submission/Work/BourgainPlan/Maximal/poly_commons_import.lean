import Mathlib
import Submission.Work.BourgainPlan.Maximal.l2_defs
import Submission.Commons.Analysis.ExponentialSums.quadratic_kernel_model_maximal_l2
import Submission.Commons.Analysis.ExponentialSums.integer_poly_complete_sum_bound
import Submission.Commons.Analysis.ExponentialSums.pure_power_kernel_maximal_l2
import Submission.Commons.Analysis.Oscillatory.van_der_corput_bound
import Submission.Commons.Analysis.Oscillatory.vt_oscillatory_integral
import Submission.Commons.Analysis.Fourier.maximal_l2_of_summable_multiplier_family

/-!
# Re-export of the commons toolkit for the general-polynomial model maximal inequality

This module exists only so that delegated statements can list a single import
(`Submission.Work.BourgainPlan.Maximal.poly_commons_import`) that brings into scope
`perNbhd`, `blockPair`, `weighted_core_maximal`, `CircleNeighborhoodMaximal`,
`integer_poly_complete_sum_bound`, `van_der_corput_bound`,
`maximal_l2_of_summable_multiplier_family` and `polyProfile`.
-/
