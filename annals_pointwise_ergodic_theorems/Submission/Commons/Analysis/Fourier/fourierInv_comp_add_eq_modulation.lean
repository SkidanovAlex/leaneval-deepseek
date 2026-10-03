import Mathlib
import Submission.Commons.Analysis.Fourier.bourgain_smooth_window_maximal_l2

open MeasureTheory
open scoped FourierTransform

namespace Commons.Analysis.Fourier

theorem fourierInv_comp_add_eq_modulation (A : ℝ → ℂ) (t y : ℝ) :
    FourierTransform.fourierInv (fun ξ : ℝ => A (ξ + t)) y
      = Complex.exp (-(2 * Real.pi * Complex.I * ((t * y : ℝ) : ℂ)))
          * FourierTransform.fourierInv A y := by
  rw [Real.fourierInv_eq_fourier_neg, Real.fourierInv_eq_fourier_neg]
  rw [fourier_comp_add A t (-y)]
  congr 1
  congr 1
  push_cast
  ring

end Commons.Analysis.Fourier
