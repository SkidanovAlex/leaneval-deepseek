import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Fourier.FourierTransform

namespace Commons.Analysis.Fourier

open MeasureTheory
open scoped FourierTransform

/-- The Fourier transform on `ℝ`, in Mathlib's `e^{-2πi}` convention, written with the
unnormalised phase `e^{-i (2π p) t}`:
`𝓕 g p = ∫ t, g t * exp (-(I * (2 π p) * t))`. -/
theorem fourier_eq_integral_exp_real (g : ℝ → ℂ) (p : ℝ) :
    𝓕 g p = ∫ t : ℝ, g t * Complex.exp (-(Complex.I * ((2 * Real.pi * p : ℝ) : ℂ) * (t : ℂ))) := by
  rw [Real.fourier_real_eq_integral_exp_smul]
  simp only [smul_eq_mul]
  congr 1
  ext t
  rw [mul_comm]
  congr 1
  push_cast
  ring

end Commons.Analysis.Fourier