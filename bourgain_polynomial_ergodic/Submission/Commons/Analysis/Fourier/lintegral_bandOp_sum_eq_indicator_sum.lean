import Mathlib
import Submission.Commons.Analysis.Fourier.bandSum_indicatorSum_l2

namespace Commons.Analysis.Fourier

open MeasureTheory Filter
open scoped BigOperators ENNReal FourierTransform Topology

noncomputable section

/-- **Plancherel for a finite sum of band-pass operators** (`Finset`-indexed version of
`Commons.Analysis.Fourier.bandSum_indicatorSum_l2`).  For measurable bounded frequency sets `C i`
and `u i ∈ L¹ ∩ L²`,
`∫⁻ ‖∑_{i∈J} bandOp (C i) (u i)‖ₑ² = ∫⁻ ‖∑_{i∈J} 1_{C i} · 𝓕 (u i)‖ₑ²`
(as integrals against `volume` on `ℝ`).

Indeed `∑_{i∈J} bandOp (C i) (u i) = 𝓕⁻ (∑_{i∈J} 1_{C i} · 𝓕 (u i))` and `𝓕⁻` is an isometry of
`L²`; the finite sum `∑_{i∈J} 1_{C i} · 𝓕 (u i)` lies in `L¹ ∩ L²` because each `C i` is bounded
and `𝓕 (u i)` is bounded. -/
theorem lintegral_bandOp_sum_eq_indicator_sum {ι : Type*} (J : Finset ι) (C : ι → Set ℝ)
    (hmeas : ∀ i, MeasurableSet (C i)) (hbd : ∀ i, Bornology.IsBounded (C i))
    (u : ι → ℝ → ℂ)
    (hu1 : ∀ i ∈ J, MeasureTheory.MemLp (u i) 1 (MeasureTheory.volume : MeasureTheory.Measure ℝ))
    (hu2 : ∀ i ∈ J, MeasureTheory.MemLp (u i) 2 (MeasureTheory.volume : MeasureTheory.Measure ℝ)) :
    ∫⁻ x : ℝ, ‖∑ i ∈ J, bandOp (C i) (u i) x‖ₑ ^ (2:ℝ) ∂MeasureTheory.volume
      = ∫⁻ ξ : ℝ, ‖∑ i ∈ J, Set.indicator (C i) (FourierTransform.fourier (u i)) ξ‖ₑ ^ (2:ℝ)
          ∂MeasureTheory.volume := by
  classical
  set g : ι → ℝ → ℂ := fun i => Set.indicator (C i) (𝓕 (u i)) with hg
  have hg1 : ∀ i ∈ J, MemLp (g i) 1 (volume : Measure ℝ) := fun i hi =>
    memLp_one_indicator_fourier (C i) (hmeas i) (hbd i) (u i)
      (memLp_one_iff_integrable.mp (hu1 i hi))
  have hF2 : ∀ i ∈ J, MemLp (𝓕 (u i)) 2 (volume : Measure ℝ) := fun i hi =>
    (Lp.memLp (𝓕 ((hu2 i hi).toLp (u i)))).ae_eq
      (fourier_toLp_ae_eq_fourier_of_memLp (hu1 i hi) (hu2 i hi))
  have hg2 : ∀ i ∈ J, MemLp (g i) 2 (volume : Measure ℝ) := fun i hi => by
    rw [hg]
    exact lt_of_le_of_lt (eLpNorm_indicator_le (𝓕 (u i)) (hmeas i)) (hF2 i hi).eLpNorm_lt_top
  have hgint : ∀ i ∈ J, Integrable (g i) (volume : Measure ℝ) := fun i hi =>
    memLp_one_iff_integrable.mp (hg1 i hi)
  have hG1 : MemLp (∑ i ∈ J, g i) 1 (volume : Measure ℝ) :=
    memLp_finsetSum' J hg1
  have hG2 : MemLp (∑ i ∈ J, g i) 2 (volume : Measure ℝ) :=
    memLp_finsetSum' J hg2
  have hlin : ∀ x : ℝ, 𝓕⁻ (∑ i ∈ J, g i) x = ∑ i ∈ J, 𝓕⁻ (g i) x :=
    fun x => fourierInv_finsetSum_apply J g hgint x
  have hpt : ∀ x : ℝ, (∑ i ∈ J, bandOp (C i) (u i) x) = 𝓕⁻ (∑ i ∈ J, g i) x := by
    intro x
    rw [hlin x]
    apply Finset.sum_congr rfl
    intro i _
    simp only [hg, bandOp]
  calc ∫⁻ x, ‖∑ i ∈ J, bandOp (C i) (u i) x‖ₑ ^ (2:ℝ)
      = ∫⁻ x, ‖𝓕⁻ (∑ i ∈ J, g i) x‖ₑ ^ (2:ℝ) :=
        lintegral_congr (fun x => by rw [hpt x])
    _ = ∫⁻ x, ‖(∑ i ∈ J, g i) x‖ₑ ^ (2:ℝ) := lintegral_enorm_fourierInv_eq hG1 hG2
    _ = ∫⁻ x, ‖∑ i ∈ J, g i x‖ₑ ^ (2:ℝ) := by
        refine lintegral_congr (fun x => ?_)
        rw [Finset.sum_apply]
    _ = ∫⁻ ξ : ℝ, ‖∑ i ∈ J,
          Set.indicator (C i) (FourierTransform.fourier (u i)) ξ‖ₑ ^ (2:ℝ) := by
        refine lintegral_congr (fun x => ?_)
        have hfun : (∑ i ∈ J, g i x) = ∑ i ∈ J,
            Set.indicator (C i) (FourierTransform.fourier (u i)) x := by
          apply Finset.sum_congr rfl
          intro i _
          rw [hg]
        rw [hfun]

end

end Commons.Analysis.Fourier
