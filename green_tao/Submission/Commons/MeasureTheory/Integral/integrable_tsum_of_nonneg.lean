import Mathlib.MeasureTheory.Integral.DominatedConvergence

open MeasureTheory
open scoped ENNReal NNReal

namespace Commons.MeasureTheory.Integral

theorem integrable_tsum_of_nonneg {ι α : Type*} [Countable ι] [MeasurableSpace α]
    {μ : MeasureTheory.Measure α} {f : ι → α → ℝ}
    (hf : ∀ i, MeasureTheory.AEStronglyMeasurable (f i) μ) (hnn : ∀ i a, 0 ≤ f i a)
    (hfin : (∑' i, MeasureTheory.lintegral μ fun a => ENNReal.ofReal (f i a)) ≠ ⊤) :
    MeasureTheory.Integrable (fun a => ∑' i, f i a) μ ∧
      MeasureTheory.integral μ (fun a => ∑' i, f i a)
        = ∑' i, MeasureTheory.integral μ fun a => f i a := by
  classical
  set F : α → ℝ≥0∞ := fun a => ∑' i, ENNReal.ofReal (f i a) with hF
  have hFmeas : AEMeasurable F μ := by
    rw [hF]
    simp_rw [ENNReal.tsum_eq_iSup_sum]
    exact AEMeasurable.iSup fun s => Finset.aemeasurable_fun_sum s fun i _ =>
      ENNReal.measurable_ofReal.comp_aemeasurable (hf i).aemeasurable
  have hFint : ∫⁻ a, F a ∂μ = ∑' i, ∫⁻ a, ENNReal.ofReal (f i a) ∂μ := by
    rw [hF]
    exact lintegral_tsum fun i =>
      ENNReal.measurable_ofReal.comp_aemeasurable (hf i).aemeasurable
  have hFne : ∫⁻ a, F a ∂μ ≠ ⊤ := by rw [hFint]; exact hfin
  have hFlt : ∀ᵐ a ∂μ, F a < ⊤ := ae_lt_top' hFmeas hFne
  have hsumm : ∀ᵐ a ∂μ, Summable (fun i => f i a) := by
    filter_upwards [hFlt] with a ha
    have hcoe : (∑' i, ((Real.toNNReal (f i a) : ℝ≥0) : ℝ≥0∞)) ≠ ∞ := ha.ne
    have hs : Summable (fun i => Real.toNNReal (f i a)) :=
      ENNReal.tsum_coe_ne_top_iff_summable.1 hcoe
    have hs2 : Summable (fun i => ((Real.toNNReal (f i a) : ℝ≥0) : ℝ)) :=
      NNReal.summable_coe.2 hs
    refine hs2.congr fun i => ?_
    rw [Real.toNNReal_of_nonneg (hnn i a)]
    rfl
  have hofReal : ∀ᵐ a ∂μ, ENNReal.ofReal (∑' i, f i a) = F a := by
    filter_upwards [hsumm] with a ha
    rw [hF]
    exact ENNReal.ofReal_tsum_of_nonneg (fun i => hnn i a) ha
  have hToReal : (fun a => (F a).toReal) =ᵐ[μ] fun a => ∑' i, f i a := by
    filter_upwards [hofReal] with a ha
    rw [← ha, ENNReal.toReal_ofReal (tsum_nonneg (fun i => hnn i a))]
  have hAESM : AEStronglyMeasurable (fun a => ∑' i, f i a) μ :=
    (hFmeas.ennreal_toReal.aestronglyMeasurable).congr hToReal
  have hHFI : HasFiniteIntegral (fun a => ∑' i, f i a) μ :=
    (hasFiniteIntegral_toReal_of_lintegral_ne_top hFne).congr hToReal
  have hint : ∫ a, ∑' i, f i a ∂μ = ∑' i, ∫ a, f i a ∂μ := by
    refine integral_tsum hf ?_
    have hcongr : ∀ i, ∫⁻ a, ‖f i a‖ₑ ∂μ = ∫⁻ a, ENNReal.ofReal (f i a) ∂μ := by
      intro i
      exact lintegral_congr fun a => Real.enorm_of_nonneg (hnn i a)
    rw [tsum_congr hcongr]
    exact hfin
  exact ⟨⟨hAESM, hHFI⟩, hint⟩

end Commons.MeasureTheory.Integral