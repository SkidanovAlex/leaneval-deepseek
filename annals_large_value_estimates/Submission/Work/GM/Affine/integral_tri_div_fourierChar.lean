import Mathlib
import Submission.Work.GM.Affine.low_freq_defs

open MeasureTheory Real

namespace Work.GM.Affine

/-- Fourier transform pair for the rescaled triangle (Fejér) kernel:
`∫ tri(ξ/A) e(s ξ) dξ = A · sinc(π A s)²`, where `e(x) = Real.fourierChar x`.

This is the change of variables `ξ = A y` applied to `integral_tri_mul_exp` together
with the evenness of `tri` and of `sinc`. -/
theorem integral_tri_div_fourierChar {A : ℝ} (hA : 0 < A) (s : ℝ) :
    ∫ ξ : ℝ, ((Commons.Analysis.Fourier.tri (ξ / A) : ℝ) : ℂ) * (Real.fourierChar (s * ξ) : ℂ)
      = ((A * Real.sinc (Real.pi * (A * s)) ^ 2 : ℝ) : ℂ) := by
  simp only [Real.fourierChar_apply]
  set g : ℝ → ℂ := fun y => ↑(Commons.Analysis.Fourier.tri y)
      * Complex.exp (↑(2 * Real.pi * (s * (A * y))) * Complex.I) with hg
  have hcomp : (∫ ξ : ℝ, ↑(Commons.Analysis.Fourier.tri (ξ / A))
        * Complex.exp (↑(2 * Real.pi * (s * ξ)) * Complex.I)) = ∫ ξ : ℝ, g (ξ / A) := by
    apply integral_congr_ae
    filter_upwards with ξ
    simp only [hg]
    congr 1
    rw [show A * (ξ / A) = ξ by field_simp]
  rw [hcomp, MeasureTheory.Measure.integral_comp_div g A]
  have hI : ∫ y : ℝ, g y = ((Real.sinc (Real.pi * (A * s)) ^ 2 : ℝ) : ℂ) := by
    have hpt : ∀ y : ℝ, g y = ↑(Commons.Analysis.Fourier.tri y)
          * Complex.exp (↑(-(2 * Real.pi * y * (-(A*s)))) * Complex.I) := by
      intro y
      simp only [hg]
      congr 2
      push_cast
      ring
    rw [integral_congr_ae (Filter.Eventually.of_forall hpt),
      Commons.Analysis.Fourier.integral_tri_mul_exp (-(A*s))]
    rw [show Real.pi * (-(A*s)) = -(Real.pi * (A*s)) by ring, Real.sinc_neg]
  rw [hI, abs_of_pos hA, Complex.real_smul, ← Complex.ofReal_mul]

end Work.GM.Affine
