import Mathlib
import Submission.Work.GM.Affine.setup
import Submission.Commons.Analysis.Fourier.fejer_window_localization_majorant

/-!
# Shared imports for the `low_freq_ge_local_mass` development

This module only re-exports the Fejér/triangle-kernel library of `Submission.Commons`
(`Commons.Analysis.Fourier.tri`, `integral_tri_mul_exp`, `sinc_pi_sq_lower_bound`, ...)
together with the §9 setup of `Submission.Work.GM.Affine.setup`, so that lemmas about
`Fhat` and the triangle kernel can be delegated against a single known-good module name.
-/
