import Mathlib
import Submission.Commons.Analysis.Fourier.fourierInv_toLp_ae_eq_fourierInv

namespace Work.BourgainPlan.Maximal

open MeasureTheory FourierTransform
open scoped FourierTransform ComplexInnerProductSpace

/-- For `L²` classes `f, g` on `ℝ`, the pointwise integral `∫ (f x) * star (g x)` is the `L²`
inner product `⟪g, f⟫`.  (This is `Lp.inner_def` together with `RCLike.inner_apply`.) -/
lemma integral_mul_star_coeFn_eq_inner (f g : Lp ℂ 2 (volume : Measure ℝ)) :
    (∫ x : ℝ, (f : ℝ → ℂ) x * star ((g : ℝ → ℂ) x)) = ⟪g, f⟫ := by
  rw [MeasureTheory.L2.inner_def]
  apply integral_congr_ae
  filter_upwards with x
  rw [RCLike.inner_apply]
  rfl

theorem plancherel_fourier_inner (A B : ℝ → ℂ) (hA1 : MeasureTheory.Integrable A)
    (hA2 : MeasureTheory.MemLp A 2 (MeasureTheory.volume : MeasureTheory.Measure ℝ))
    (hB1 : MeasureTheory.Integrable B)
    (hB2 : MeasureTheory.MemLp B 2 (MeasureTheory.volume : MeasureTheory.Measure ℝ)) :
    (∫ x : ℝ, FourierTransformInv.fourierInv A x * star (FourierTransformInv.fourierInv B x))
      = ∫ ξ : ℝ, A ξ * star (B ξ) := by
  have hA1' : MeasureTheory.MemLp A 1 (MeasureTheory.volume : MeasureTheory.Measure ℝ) :=
    MeasureTheory.memLp_one_iff_integrable.mpr hA1
  have hB1' : MeasureTheory.MemLp B 1 (MeasureTheory.volume : MeasureTheory.Measure ℝ) :=
    MeasureTheory.memLp_one_iff_integrable.mpr hB1
  have hAae := Commons.Analysis.Fourier.fourierInv_toLp_ae_eq_fourierInv (V := ℝ) hA1' hA2
  have hBae := Commons.Analysis.Fourier.fourierInv_toLp_ae_eq_fourierInv (V := ℝ) hB1' hB2
  calc (∫ x : ℝ, FourierTransformInv.fourierInv A x * star (FourierTransformInv.fourierInv B x))
      = ∫ x : ℝ, ((𝓕⁻ (hA2.toLp A) : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ) x
          * star (((𝓕⁻ (hB2.toLp B) : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ) x) := by
        apply integral_congr_ae
        filter_upwards [hAae, hBae] with x hx hy
        rw [hx, hy]
    _ = ⟪𝓕⁻ (hB2.toLp B), 𝓕⁻ (hA2.toLp A)⟫ :=
        integral_mul_star_coeFn_eq_inner _ _
    _ = ⟪hB2.toLp B, hA2.toLp A⟫ := by
        rw [← MeasureTheory.Lp.inner_fourier_eq (𝓕⁻ (hB2.toLp B)) (𝓕⁻ (hA2.toLp A))]
        rw [FourierInvPair.fourier_fourierInv_eq, FourierInvPair.fourier_fourierInv_eq]
    _ = ∫ ξ : ℝ, A ξ * star (B ξ) := by
        rw [← integral_mul_star_coeFn_eq_inner (hA2.toLp A) (hB2.toLp B)]
        apply integral_congr_ae
        filter_upwards [hA2.coeFn_toLp, hB2.coeFn_toLp] with x hx hy
        rw [hx, hy]

end Work.BourgainPlan.Maximal
