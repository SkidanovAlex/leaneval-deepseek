import Mathlib
import Submission.Commons.Analysis.Fourier.nested_scales_maximal_l2_real
import Submission.Commons.Analysis.Fourier.boundary_layer_l2

namespace Commons.Analysis.Fourier

open MeasureTheory Filter
open scoped BigOperators ENNReal FourierTransform Topology RealInnerProductSpace

noncomputable section

/-- The integrand of the inverse Fourier integral of an `L¹` function is again integrable: the
oscillatory factor has modulus one. -/
lemma integrable_exp_smul_I {f : ℝ → ℂ} (hf : Integrable f (volume : Measure ℝ)) (x : ℝ) :
    Integrable (fun v : ℝ =>
      Complex.exp ((↑(2 * Real.pi * (v * x)) : ℂ) * Complex.I) • f v) (volume : Measure ℝ) := by
  refine (hf.norm).mono' ?_ ?_
  · exact ((by fun_prop : Continuous fun v : ℝ =>
        Complex.exp ((↑(2 * Real.pi * (v * x)) : ℂ) * Complex.I))).aestronglyMeasurable.smul
      hf.aestronglyMeasurable
  · filter_upwards with v
    rw [norm_smul, Complex.norm_exp_ofReal_mul_I, one_mul]

/-- The inverse Fourier transform is additive, pointwise, on finite sums of integrable
functions. -/
lemma fourierInv_finsetSum_apply {ι : Type*} (s : Finset ι) (f : ι → ℝ → ℂ)
    (hf : ∀ i ∈ s, Integrable (f i) (volume : Measure ℝ)) (x : ℝ) :
    𝓕⁻ (∑ i ∈ s, f i) x = ∑ i ∈ s, 𝓕⁻ (f i) x := by
  have hkey : ∀ i ∈ s, Integrable (fun v : ℝ =>
      Complex.exp ((↑(2 * Real.pi * (v * x)) : ℂ) * Complex.I) • f i v) (volume : Measure ℝ) :=
    fun i hi => integrable_exp_smul_I (hf i hi) x
  have hL : 𝓕⁻ (∑ i ∈ s, f i) x = ∫ v : ℝ,
      Complex.exp ((↑(2 * Real.pi * (v * x)) : ℂ) * Complex.I) • (∑ i ∈ s, f i) v := by
    rw [Real.fourierInv_eq']
    apply integral_congr_ae
    filter_upwards with v
    congr 1
    rw [Real.inner_apply]
  have hR : (∑ i ∈ s, 𝓕⁻ (f i) x) = ∑ i ∈ s, ∫ v : ℝ,
      Complex.exp ((↑(2 * Real.pi * (v * x)) : ℂ) * Complex.I) • f i v := by
    apply Finset.sum_congr rfl
    intro i _
    rw [Real.fourierInv_eq']
    apply integral_congr_ae
    filter_upwards with v
    congr 1
    rw [Real.inner_apply]
  rw [hL, hR]
  simp only [Finset.sum_apply, Finset.smul_sum]
  rw [integral_finsetSum s hkey]

lemma bandSum_indicatorSum_l2 {M : ℕ} (C : Fin M → Set ℝ)
    (hmeas : ∀ i, MeasurableSet (C i)) (hbd : ∀ i, Bornology.IsBounded (C i))
    (u : Fin M → ℝ → ℂ) (hu1 : ∀ i, MeasureTheory.MemLp (u i) 1 (MeasureTheory.volume : MeasureTheory.Measure ℝ))
    (hu2 : ∀ i, MeasureTheory.MemLp (u i) 2 (MeasureTheory.volume : MeasureTheory.Measure ℝ)) :
    MeasureTheory.lintegral (MeasureTheory.volume : MeasureTheory.Measure ℝ)
        (fun x : ℝ => enorm (∑ i : Fin M, bandOp (C i) (u i) x) ^ (2:ℝ))
      = MeasureTheory.lintegral (MeasureTheory.volume : MeasureTheory.Measure ℝ)
        (fun ξ : ℝ => enorm (∑ i : Fin M, Set.indicator (C i) (FourierTransform.fourier (u i)) ξ) ^ (2:ℝ)) := by
  classical
  set g : Fin M → ℝ → ℂ := fun i => Set.indicator (C i) (𝓕 (u i)) with hg
  have hg1 : ∀ i, MemLp (g i) 1 (volume : Measure ℝ) := fun i =>
    memLp_one_indicator_fourier (C i) (hmeas i) (hbd i) (u i)
      (memLp_one_iff_integrable.mp (hu1 i))
  have hF2 : ∀ i, MemLp (𝓕 (u i)) 2 (volume : Measure ℝ) := fun i =>
    (Lp.memLp (𝓕 ((hu2 i).toLp (u i)))).ae_eq
      (fourier_toLp_ae_eq_fourier_of_memLp (hu1 i) (hu2 i))
  have hg2 : ∀ i, MemLp (g i) 2 (volume : Measure ℝ) := fun i => by
    rw [hg]
    exact lt_of_le_of_lt (eLpNorm_indicator_le (𝓕 (u i)) (hmeas i)) (hF2 i).eLpNorm_lt_top
  have hgint : ∀ i, Integrable (g i) (volume : Measure ℝ) := fun i =>
    memLp_one_iff_integrable.mp (hg1 i)
  have hG1 : MemLp (∑ i : Fin M, g i) 1 (volume : Measure ℝ) :=
    memLp_finsetSum' _ (fun i _ => hg1 i)
  have hG2 : MemLp (∑ i : Fin M, g i) 2 (volume : Measure ℝ) :=
    memLp_finsetSum' _ (fun i _ => hg2 i)
  have hlin : ∀ x : ℝ, 𝓕⁻ (∑ i : Fin M, g i) x = ∑ i : Fin M, 𝓕⁻ (g i) x :=
    fun x => fourierInv_finsetSum_apply Finset.univ g (fun i _ => hgint i) x
  have hpt : ∀ x : ℝ, (∑ i : Fin M, bandOp (C i) (u i) x) = 𝓕⁻ (∑ i : Fin M, g i) x := by
    intro x
    rw [hlin x]
    apply Finset.sum_congr rfl
    intro i _
    simp only [hg, bandOp]
  calc ∫⁻ x, ‖∑ i : Fin M, bandOp (C i) (u i) x‖ₑ ^ (2:ℝ)
      = ∫⁻ x, ‖𝓕⁻ (∑ i : Fin M, g i) x‖ₑ ^ (2:ℝ) :=
        lintegral_congr (fun x => by rw [hpt x])
    _ = ∫⁻ x, ‖(∑ i : Fin M, g i) x‖ₑ ^ (2:ℝ) := lintegral_enorm_fourierInv_eq hG1 hG2
    _ = ∫⁻ x, ‖∑ i : Fin M, g i x‖ₑ ^ (2:ℝ) := by
        refine lintegral_congr (fun x => ?_)
        rw [Finset.sum_apply]
    _ = ∫⁻ ξ : ℝ, ‖∑ i : Fin M,
          Set.indicator (C i) (FourierTransform.fourier (u i)) ξ‖ₑ ^ (2:ℝ) := by
        refine lintegral_congr (fun x => ?_)
        have hfun : (∑ i : Fin M, g i x) = ∑ i : Fin M,
            Set.indicator (C i) (FourierTransform.fourier (u i)) x := by
          apply Finset.sum_congr rfl
          intro i _
          rw [hg]
        rw [hfun]

end
end Commons.Analysis.Fourier
