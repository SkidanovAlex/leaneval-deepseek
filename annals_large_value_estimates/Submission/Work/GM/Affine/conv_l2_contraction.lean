import Mathlib
import Submission.Work.GM.Affine.setup

namespace Work.GM.Affine

open MeasureTheory
open scoped Convolution

theorem conv_l2_contraction {φ f : ℝ → ℝ} (hφnn : ∀ x, 0 ≤ φ x) (hφc : Continuous φ)
    (hφcs : HasCompactSupport φ) (hφ1 : ∫ x, φ x = 1)
    (hfn : ∀ u, 0 ≤ f u) (hfi : MeasureTheory.Integrable f)
    (hfi2 : MeasureTheory.Integrable (fun u => (f u) ^ 2)) :
    ∫ u, (MeasureTheory.convolution φ f (ContinuousLinearMap.lsmul ℝ ℝ) MeasureTheory.volume u) ^ 2
      ≤ ∫ u, (f u) ^ 2 := by
  set k : ℝ → ENNReal := fun t => ENNReal.ofReal (φ t) with hk
  have hk_meas : Measurable k := by rw [hk]; exact hφc.measurable.ennreal_ofReal
  have hk_lt : ∀ᵐ t ∂(volume : Measure ℝ), k t < ⊤ :=
    Filter.Eventually.of_forall fun t => by rw [hk]; exact ENNReal.ofReal_lt_top
  have hφi : Integrable φ := hφc.integrable_of_hasCompactSupport hφcs
  have hfuniv : (volume.withDensity k) Set.univ = 1 := by
    rw [withDensity_apply k MeasurableSet.univ, setLIntegral_univ, hk,
      ← ofReal_integral_eq_lintegral_ofReal hφi (Filter.Eventually.of_forall hφnn), hφ1]
    simp
  haveI : IsProbabilityMeasure (volume.withDensity k) := ⟨hfuniv⟩
  -- the convolution as an integral against the probability measure `volume.withDensity k`
  have hconv : ∀ u, convolution φ f (ContinuousLinearMap.lsmul ℝ ℝ) volume u
      = ∫ t, f (u - t) ∂(volume.withDensity k) := by
    intro u
    rw [convolution_def, integral_withDensity_eq_integral_toReal_smul hk_meas hk_lt]
    refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
    simp only [ContinuousLinearMap.lsmul_apply, hk]
    rw [ENNReal.toReal_ofReal (hφnn t)]
  -- a.e. integrability of the two integrands of Jensen
  have hgood1 : ∀ᵐ u ∂(volume : Measure ℝ),
      Integrable (fun t => f (u - t)) (volume.withDensity k) := by
    filter_upwards [hφi.ae_convolution_exists (L := ContinuousLinearMap.lsmul ℝ ℝ) hfi]
      with u hu
    refine (integrable_withDensity_iff_integrable_smul' hk_meas hk_lt).2 ?_
    refine hu.congr (Filter.Eventually.of_forall fun t => ?_)
    simp only [ContinuousLinearMap.lsmul_apply, hk]
    rw [ENNReal.toReal_ofReal (hφnn t)]
  have hgood2 : ∀ᵐ u ∂(volume : Measure ℝ),
      Integrable (fun t => (f (u - t)) ^ 2) (volume.withDensity k) := by
    filter_upwards [hφi.ae_convolution_exists (L := ContinuousLinearMap.lsmul ℝ ℝ)
      (g := fun t => (f t) ^ 2) hfi2] with u hu
    refine (integrable_withDensity_iff_integrable_smul' hk_meas hk_lt).2 ?_
    refine hu.congr (Filter.Eventually.of_forall fun t => ?_)
    simp only [ContinuousLinearMap.lsmul_apply, hk]
    rw [ENNReal.toReal_ofReal (hφnn t)]
  have hgood : ∀ᵐ u ∂(volume : Measure ℝ),
      Integrable (fun t => f (u - t)) (volume.withDensity k) ∧
        Integrable (fun t => (f (u - t)) ^ 2) (volume.withDensity k) := hgood1.and hgood2
  -- Jensen's inequality, pointwise a.e.
  have hJensen : ∀ᵐ u ∂(volume : Measure ℝ),
      (convolution φ f (ContinuousLinearMap.lsmul ℝ ℝ) volume u) ^ 2
        ≤ ∫ t, (f (u - t)) ^ 2 ∂(volume.withDensity k) := by
    filter_upwards [hgood] with u hu
    obtain ⟨hu1, hu2⟩ := hu
    have hjen := ConvexOn.map_integral_le (μ := volume.withDensity k)
      (s := Set.Ici 0) (g := fun y : ℝ => y ^ 2) (f := fun t => f (u - t))
      (convexOn_pow 2) (continuous_pow 2).continuousOn isClosed_Ici
      (Filter.Eventually.of_forall fun t => hfn (u - t)) hu1 hu2
    rw [hconv u]
    exact hjen
  -- the right hand side is integrable (it is a convolution)
  have hRpoint : ∀ u, (∫ t, (f (u - t)) ^ 2 ∂(volume.withDensity k))
      = convolution φ (fun t => (f t) ^ 2) (ContinuousLinearMap.lsmul ℝ ℝ) volume u := by
    intro u
    rw [convolution_def, integral_withDensity_eq_integral_toReal_smul hk_meas hk_lt]
    refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
    simp only [ContinuousLinearMap.lsmul_apply, hk]
    rw [ENNReal.toReal_ofReal (hφnn t)]
  have hRint : Integrable (fun u => ∫ t, (f (u - t)) ^ 2 ∂(volume.withDensity k)) volume := by
    rw [show (fun u => ∫ t, (f (u - t)) ^ 2 ∂(volume.withDensity k))
        = (fun u => convolution φ (fun t => (f t) ^ 2)
            (ContinuousLinearMap.lsmul ℝ ℝ) volume u) from funext hRpoint]
    exact Integrable.integrable_convolution (L := ContinuousLinearMap.lsmul ℝ ℝ) hφi hfi2
  have hLint : Integrable
      (fun u => (convolution φ f (ContinuousLinearMap.lsmul ℝ ℝ) volume u) ^ 2) volume := by
    refine Integrable.mono' hRint ?_ ?_
    · exact (Integrable.integrable_convolution (L := ContinuousLinearMap.lsmul ℝ ℝ) hφi hfi).aestronglyMeasurable.pow 2
    · filter_upwards [hJensen] with u hu
      rw [Real.norm_of_nonneg (sq_nonneg _)]
      exact hu
  have hmain : ∫ u, (convolution φ f (ContinuousLinearMap.lsmul ℝ ℝ) volume u) ^ 2
      ≤ ∫ u, ∫ t, (f (u - t)) ^ 2 ∂(volume.withDensity k) :=
    integral_mono_ae hLint hRint hJensen
  calc ∫ u, (convolution φ f (ContinuousLinearMap.lsmul ℝ ℝ) volume u) ^ 2
      ≤ ∫ u, ∫ t, (f (u - t)) ^ 2 ∂(volume.withDensity k) := hmain
    _ = ∫ u, convolution φ (fun t => (f t) ^ 2)
          (ContinuousLinearMap.lsmul ℝ ℝ) volume u := by
        rw [show (fun u => ∫ t, (f (u - t)) ^ 2 ∂(volume.withDensity k))
            = (fun u => convolution φ (fun t => (f t) ^ 2)
                (ContinuousLinearMap.lsmul ℝ ℝ) volume u) from funext hRpoint]
    _ = ∫ u, (f u) ^ 2 := by
        rw [integral_convolution (L := ContinuousLinearMap.lsmul ℝ ℝ) hφi hfi2]
        simp only [ContinuousLinearMap.lsmul_apply, hφ1, one_smul]

end Work.GM.Affine
