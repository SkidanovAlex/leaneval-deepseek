import Mathlib
import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
import Submission.Commons.Analysis.SpecialFunctions.Gamma.digamma_logRem_Binet
import Submission.Commons.Analysis.SpecialFunctions.Gamma.digamma_logRem_kernel_nonneg
import Submission.Commons.Analysis.SpecialFunctions.Gamma.digamma_logRem_kernelIntegral

open Complex Filter Set MeasureTheory
open scoped Real Topology BigOperators

noncomputable section

namespace Commons.Analysis.SpecialFunctions.Gamma

theorem digamma_logRem_le (x y : ℝ) (hx1 : (1 : ℝ) / 2 ≤ x) (hx2 : x ≤ 8) :
    ‖Complex.digamma ((x : ℂ) + (y : ℂ) * Complex.I) -
        Complex.log ((x : ℂ) + (y : ℂ) * Complex.I) +
        ((2 : ℂ)⁻¹) * (((x : ℂ) + (y : ℂ) * Complex.I)⁻¹)‖ ≤ (1 : ℝ) / 2 := by
  let z : ℂ := (x : ℂ) + (y : ℂ) * Complex.I
  let ker : ℝ → ℝ := fun t => 1 / (Real.exp t - 1) - 1 / t + 1 / 2
  have hz : 0 < z.re := by
    dsimp [z]
    simp
    linarith
  have hB : Complex.digamma z - Complex.log z + ((2 : ℂ)⁻¹) * z⁻¹ =
      -∫ t in Ioi (0 : ℝ), (ker t : ℂ) * Complex.exp (-(z * (t : ℂ))) := by
    dsimp [ker]
    exact digamma_logRem_Binet z hz
  have hpt : ∀ t ∈ Ioi (0 : ℝ),
      ‖(ker t : ℂ) * Complex.exp (-(z * (t : ℂ)))‖ = ker t * Real.exp (-x * t) := by
    intro t ht
    have ht0 : 0 < t := ht
    have hker : 0 ≤ ker t := digamma_logRem_kernel_nonneg ht0
    have hrexp : (-(z * (t : ℂ))).re = -x * t := by
      simp [z]
    rw [norm_mul, Complex.norm_exp, hrexp]
    have hn1 : ‖(ker t : ℂ)‖ = ker t := by
      rw [Complex.norm_real, Real.norm_eq_abs]
      exact abs_of_nonneg hker
    rw [hn1]
  calc
    ‖Complex.digamma ((x : ℂ) + (y : ℂ) * Complex.I) -
        Complex.log ((x : ℂ) + (y : ℂ) * Complex.I) +
        ((2 : ℂ)⁻¹) * (((x : ℂ) + (y : ℂ) * Complex.I)⁻¹)‖
        = ‖Complex.digamma z - Complex.log z + ((2 : ℂ)⁻¹) * z⁻¹‖ := by
          simp [z]
    _ = ‖∫ t in Ioi (0 : ℝ), (ker t : ℂ) * Complex.exp (-(z * (t : ℂ)))‖ := by
          rw [hB]
          simp
    _ ≤ ∫ t in Ioi (0 : ℝ), ‖(ker t : ℂ) * Complex.exp (-(z * (t : ℂ)))‖ := by
          simpa using norm_integral_le_integral_norm
            (f := fun t : ℝ => (ker t : ℂ) * Complex.exp (-(z * (t : ℂ))))
    _ = ∫ t in Ioi (0 : ℝ), ker t * Real.exp (-x * t) := by
          apply setIntegral_congr_fun measurableSet_Ioi
          intro t ht
          exact hpt t ht
    _ ≤ (1 : ℝ) / 2 := by
          simpa [ker] using digamma_logRem_kernelIntegral x hx1

end Commons.Analysis.SpecialFunctions.Gamma
