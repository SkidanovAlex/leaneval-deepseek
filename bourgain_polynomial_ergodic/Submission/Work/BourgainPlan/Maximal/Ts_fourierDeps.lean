import Submission.Commons.Analysis.Fourier.boundary_layer_l2
import Submission.Commons.Analysis.Fourier.fourier_toLp_eq_fourier_integral
import Submission.Commons.Analysis.Fourier.fourierInv_toLp_ae_eq_fourierInv
import Submission.Commons.Analysis.Fourier.fourier_eq_zero_of_not_integrable
import Submission.Commons.Analysis.Fourier.multiplier_eq_convolution_ae
import Submission.Work.BourgainPlan.Maximal.polyProfile_fourier_dilation
import Submission.Work.BourgainPlan.Maximal.polyProfile_step_diff_decay

/-!
# Import bundle for the `L²` decay of the dyadic Littlewood–Paley operator `T_s`

Convenience re-exports of the Fourier-multiplier machinery of `Submission.Commons.Analysis.Fourier`
and of the polynomial-profile multiplier identities used by
`Submission/Work/BourgainPlan/Maximal/Ts_l2_decay.lean`.
-/
