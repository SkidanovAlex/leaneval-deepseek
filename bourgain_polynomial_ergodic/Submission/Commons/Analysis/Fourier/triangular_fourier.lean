import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc
import Submission.Commons.Analysis.Fourier.triangle_kernel_fourier_transform

namespace Commons.Analysis.Fourier

/-- The Fourier integral of the triangular (tent) function on `[-w, w]`:
`∫_{-w}^{w} (1 - |x|/w) e^{-2π i n x} dx = w · sinc(π n w)^2`.

This is obtained from the normalised case `w = 1` (`triangle_kernel_fourier_transform`)
by the scaling substitution `x = w t`. -/
theorem triangular_fourier (w : ℝ) (hw : 0 < w) (n : ℤ) :
    (∫ x in (-w)..w, ((1 - |x| / w : ℝ) : ℂ) *
        Complex.exp (-(2 * Real.pi * (n : ℝ) * x : ℝ) * Complex.I))
      = (w : ℂ) * (Real.sinc (Real.pi * (n : ℝ) * w)) ^ 2 := by
  have hscale := intervalIntegral.smul_integral_comp_mul_left
    (f := fun x : ℝ => ((1 - |x| / w : ℝ) : ℂ) *
        Complex.exp (-(2 * Real.pi * (n : ℝ) * x : ℝ) * Complex.I)) (a := -1) (b := 1) (c := w)
  rw [show w * (-1:ℝ) = -w by ring, show w * (1:ℝ) = w by ring] at hscale
  rw [← hscale]
  have hcongr : (∫ x in (-1:ℝ)..1, ((1 - |(w * x)| / w : ℝ) : ℂ) *
        Complex.exp (-(2 * Real.pi * (n : ℝ) * (w * x) : ℝ) * Complex.I))
      = ∫ x in (-1:ℝ)..1, ((1 - |x| : ℝ) : ℂ) *
        Complex.exp (-(2 * Real.pi * Complex.I * (((n : ℝ) * w : ℝ) : ℂ) * (x : ℂ))) := by
    apply intervalIntegral.integral_congr
    intro x _
    dsimp only
    have h1 : |w * x| / w = |x| := by
      rw [abs_mul, abs_of_pos hw]; field_simp
    have h2 : -(2 * Real.pi * (n : ℝ) * (w * x) : ℝ) * Complex.I
        = -(2 * Real.pi * Complex.I * (((n : ℝ) * w : ℝ) : ℂ) * (x : ℂ)) := by
      push_cast; ring
    rw [h1, h2]
  rw [hcongr, triangle_kernel_fourier_transform, Complex.real_smul]
  have key : (if ((n : ℝ) * w : ℝ) = 0 then (1:ℝ)
        else (Real.sin (Real.pi * ((n : ℝ) * w)) / (Real.pi * ((n : ℝ) * w))) ^ 2)
      = (Real.sinc (Real.pi * (n : ℝ) * w)) ^ 2 := by
    have hpi : Real.pi * ((n : ℝ) * w) = Real.pi * (n : ℝ) * w := by ring
    by_cases h : ((n : ℝ) * w : ℝ) = 0
    · have ht : Real.pi * (n : ℝ) * w = 0 := by
        rw [show Real.pi * (n : ℝ) * w = Real.pi * ((n : ℝ) * w) by ring, h, mul_zero]
      rw [if_pos h, ht, Real.sinc_zero]; norm_num
    · rw [if_neg h, ← hpi, Real.sinc_of_ne_zero (mul_ne_zero Real.pi_ne_zero h)]
  rw [key, ← Complex.ofReal_pow]

end Commons.Analysis.Fourier