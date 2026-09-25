import Mathlib
import Submission.Commons.Analysis.Fourier.fourier_toLp_eq_fourier_integral

open MeasureTheory
open scoped ENNReal FourierTransform

namespace Commons.Analysis.Fourier

/-- The `eLpNorm` (in `L²`) of an `L²` class, seen as a function, is the real norm of the class. -/
private lemma eLpNorm_coeFn_Lp_two (f : Lp ℂ 2 (volume : Measure ℝ)) :
    eLpNorm (f : ℝ → ℂ) 2 volume = ENNReal.ofReal ‖f‖ := by
  rw [Lp.norm_def, ENNReal.ofReal_toReal (Lp.eLpNorm_ne_top f)]

/-- The previous lemma, with the exponent `2` written as a coercion from `ℝ≥0`. -/
private lemma eLpNorm_coeFn_Lp_two_aux (f : Lp ℂ 2 (volume : Measure ℝ)) :
    eLpNorm (f : ℝ → ℂ) ((2 : NNReal) : ℝ≥0∞) volume = ENNReal.ofReal ‖f‖ := by
  simpa using eLpNorm_coeFn_Lp_two f

/-- The `L²` "energy" `∫⁻ x, ‖f x‖ₑ ^ 2` of an `L²` class, expressed through its norm. -/
private lemma lintegral_enorm_sq_eq_ofReal_norm_rpow (f : Lp ℂ 2 (volume : Measure ℝ)) :
    ∫⁻ x, ‖(f : ℝ → ℂ) x‖ₑ ^ (2 : ℝ) = (ENNReal.ofReal ‖f‖) ^ (2 : ℝ) := by
  have h := eLpNorm_nnreal_pow_eq_lintegral (f := (f : ℝ → ℂ)) (p := 2) (μ := volume)
    (by norm_num) (Lp.aestronglyMeasurable f)
  rw [eLpNorm_coeFn_Lp_two_aux f] at h
  exact h.symm

/-- **Plancherel for the pointwise inverse Fourier integral of an `L¹ ∩ L²` function.**  For
`h : ℝ → ℂ` in `L¹ ∩ L²`, the `L²` norm of the pointwise inverse Fourier integral
`x ↦ ∫ ξ, e^{2πi x ξ} h ξ dξ` equals the `L²` norm of `h`:
`∫⁻ x, ‖𝓕⁻ h x‖ₑ² = ∫⁻ x, ‖h x‖ₑ²`.
`𝓕⁻ h = (𝓕 h) ∘ Neg.neg`, the `L²` Fourier transform of an `L¹ ∩ L²` function is a.e. its
pointwise Fourier integral (`Commons.Analysis.Fourier.fourier_toLp_ae_eq_fourier_of_memLp`), and
composition with `Neg.neg` is an isometry of `L²` since Lebesgue measure is negation
invariant. -/
theorem lintegral_fourierInv_eq {h : ℝ → ℂ} (h1 : MeasureTheory.MemLp h 1 MeasureTheory.volume)
    (h2 : MeasureTheory.MemLp h 2 MeasureTheory.volume) :
    MeasureTheory.lintegral MeasureTheory.volume
        (fun x : ℝ => ENNReal.ofReal ‖FourierTransformInv.fourierInv h x‖ ^ (2:ℝ))
      = MeasureTheory.lintegral MeasureTheory.volume
        (fun x : ℝ => ENNReal.ofReal ‖h x‖ ^ (2:ℝ)) := by
  simp_rw [ofReal_norm]
  calc ∫⁻ x, ‖𝓕⁻ h x‖ₑ ^ (2:ℝ)
      = ∫⁻ x, ‖𝓕 h (-x)‖ₑ ^ (2:ℝ) := by simp_rw [Real.fourierInv_eq_fourier_neg]
    _ = ∫⁻ x, ‖𝓕 h x‖ₑ ^ (2:ℝ) :=
          lintegral_neg_eq_self (fun x : ℝ => ‖𝓕 h x‖ₑ ^ (2:ℝ))
    _ = ∫⁻ x, ‖(𝓕 (h2.toLp h) : Lp ℂ 2 (volume : Measure ℝ)) x‖ₑ ^ (2:ℝ) := by
          apply lintegral_congr_ae
          filter_upwards [fourier_toLp_ae_eq_fourier_of_memLp h1 h2] with x hx
          rw [← hx]
    _ = ∫⁻ x, ‖(h2.toLp h : Lp ℂ 2 (volume : Measure ℝ)) x‖ₑ ^ (2:ℝ) := by
          rw [lintegral_enorm_sq_eq_ofReal_norm_rpow (𝓕 (h2.toLp h)),
            lintegral_enorm_sq_eq_ofReal_norm_rpow (h2.toLp h), Lp.norm_fourier_eq]
    _ = ∫⁻ x, ‖h x‖ₑ ^ (2:ℝ) := by
          apply lintegral_congr_ae
          filter_upwards [h2.coeFn_toLp] with x hx
          rw [hx]

end Commons.Analysis.Fourier
