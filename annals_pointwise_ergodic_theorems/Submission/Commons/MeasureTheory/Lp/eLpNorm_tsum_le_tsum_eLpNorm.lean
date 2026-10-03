import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.Order.CompletePartialOrder
import Submission.Port.Aesm

open MeasureTheory ENNReal
open scoped ENNReal

namespace Commons.MeasureTheory.Lp

variable {α ι : Type*}

/-- For `ENNReal`-valued functions, taking a positive power commutes with an `iSup`. -/
private lemma iSup_rpow_eq {z : ℝ} (hz : 0 < z) (g : ι → ℝ≥0∞) :
    (⨆ i, g i) ^ z = ⨆ i, (g i) ^ z := by
  have h_mono := ENNReal.strictMono_rpow_of_pos hz
  have h_surj := (ENNReal.rpow_left_bijective hz.ne.symm).2
  exact (h_mono.orderIsoOfSurjective _ h_surj).map_iSup g

/-- Minkowski's inequality (finite form) for `ENNReal`-valued functions:
`(∫ (∑_{i ∈ s} fᵢ)^q)^{1/q} ≤ ∑_{i ∈ s} (∫ fᵢ^q)^{1/q}` for `q ≥ 1`. -/
private lemma finset_lintegral_rpow_sum_le {m : MeasurableSpace α} {μ : Measure α}
    {q : ℝ} (hq : 1 ≤ q) {f : ι → α → ℝ≥0∞} (hf : ∀ i, AEMeasurable (f i) μ)
    (s : Finset ι) :
    (∫⁻ a, ((∑ i ∈ s, f i) a) ^ q ∂μ) ^ (1 / q) ≤
      ∑ i ∈ s, (∫⁻ a, (f i a) ^ q ∂μ) ^ (1 / q) := by
  classical
  induction s using Finset.induction with
  | empty =>
      have hq_pos : (0 : ℝ) < q := lt_of_lt_of_le zero_lt_one hq
      rw [Finset.sum_empty, Finset.sum_empty]
      simp only [Pi.zero_apply, lintegral_zero, ENNReal.zero_rpow_of_pos hq_pos]
      rw [ENNReal.zero_rpow_of_pos (div_pos one_pos hq_pos)]
  | insert a s ha ih =>
      have hq_pos : (0 : ℝ) < q := lt_of_lt_of_le zero_lt_one hq
      have hG : AEMeasurable (∑ i ∈ s, f i) μ :=
        Finset.aemeasurable_sum s (fun i _ => hf i)
      rw [Finset.sum_insert ha, Finset.sum_insert ha]
      refine (ENNReal.lintegral_Lp_add_le (hf a) hG hq).trans ?_
      exact add_le_add le_rfl ih

/-- The target inequality: `eLpNorm` of a countable sum of `ENNReal`-valued functions is at most
the sum of the `eLpNorm`s. This is Minkowski's inequality for infinite series. -/
theorem eLpNorm_tsum_le_tsum_eLpNorm {α ι : Type*} {m : MeasurableSpace α} {μ : MeasureTheory.Measure α}
    [Countable ι] {p : ENNReal} (hp : 1 ≤ p) {f : ι → α → ENNReal}
    (hf : ∀ i, AEMeasurable (f i) μ) :
    MeasureTheory.eLpNorm (fun a => ∑' i, f i a) p μ
      ≤ ∑' i, MeasureTheory.eLpNorm (f i) p μ := by
  classical
  rcases eq_or_ne p ⊤ with rfl | hp_top
  · rw [eLpNorm_exponent_top (AEMeasurable.ennreal_tsum hf).aestronglyMeasurable]
    refine eLpNormEssSup_le_of_ae_enorm_bound ?_
    have key : ∀ᵐ a ∂μ, ∀ i, f i a ≤ eLpNorm (f i) ∞ μ := by
      rw [ae_all_iff]
      intro i
      filter_upwards [ae_le_eLpNormEssSup (f := f i) (μ := μ)] with a ha
      rw [eLpNorm_exponent_top (hf i).aestronglyMeasurable]
      simpa [enorm_eq_self] using ha
    filter_upwards [key] with a ha
    simpa [enorm_eq_self] using ENNReal.tsum_le_tsum ha
  · rcases eq_or_ne p 0 with rfl | hp0
    · rw [eLpNorm_exponent_zero (AEMeasurable.ennreal_tsum hf).aestronglyMeasurable]
      positivity
    · set q : ℝ := p.toReal with hq_def
      have hp_ne_top : p ≠ ⊤ := hp_top
      have hq1 : 1 ≤ q := by
        rw [hq_def]
        simpa using ENNReal.toReal_mono hp_ne_top hp
      have hq_pos : 0 < q := lt_of_lt_of_le zero_lt_one hq1
      have hq_ne : q ≠ 0 := hq_pos.ne'
      set A : ι → ℝ≥0∞ := fun i => (∫⁻ a, (f i a) ^ q ∂μ) ^ (1 / q) with hA
      have hmain : (∫⁻ a, (∑' i, f i a) ^ q ∂μ) ≤ (∑' i, A i) ^ q := by
        have hsup : ∀ a, (∑' i, f i a) = ⨆ s : Finset ι, ((∑ i ∈ s, f i) a) := by
          intro a
          rw [ENNReal.tsum_eq_iSup_sum]
          simp only [Finset.sum_apply]
        have h1 : (∫⁻ a, (∑' i, f i a) ^ q ∂μ)
            = ∫⁻ a, ⨆ s : Finset ι, ((∑ i ∈ s, f i) a) ^ q ∂μ := by
          refine lintegral_congr (fun a => ?_)
          rw [hsup a, iSup_rpow_eq hq_pos]
        have h2 : (∫⁻ a, ⨆ s : Finset ι, ((∑ i ∈ s, f i) a) ^ q ∂μ)
            = ⨆ s : Finset ι, ∫⁻ a, ((∑ i ∈ s, f i) a) ^ q ∂μ := by
          refine lintegral_iSup_directed (fun s => ?_) (fun s t => ?_)
          · exact (Finset.aemeasurable_sum s (fun i _ => hf i)).pow_const q
          · refine ⟨s ∪ t, ?_, ?_⟩
            · intro a
              apply ENNReal.rpow_le_rpow _ hq_pos.le
              simp only [Finset.sum_apply]
              exact Finset.sum_le_sum_of_subset_of_nonneg Finset.subset_union_left
                (fun i _ _ => bot_le)
            · intro a
              apply ENNReal.rpow_le_rpow _ hq_pos.le
              simp only [Finset.sum_apply]
              exact Finset.sum_le_sum_of_subset_of_nonneg Finset.subset_union_right
                (fun i _ _ => bot_le)
        have h3 : (⨆ s : Finset ι, ∫⁻ a, ((∑ i ∈ s, f i) a) ^ q ∂μ) ≤ (∑' i, A i) ^ q := by
          refine iSup_le (fun s => ?_)
          have hs : (∫⁻ a, ((∑ i ∈ s, f i) a) ^ q ∂μ) ^ (1 / q) ≤ ∑' i, A i :=
            (finset_lintegral_rpow_sum_le hq1 hf s).trans (ENNReal.sum_le_tsum s)
          calc (∫⁻ a, ((∑ i ∈ s, f i) a) ^ q ∂μ)
              = ((∫⁻ a, ((∑ i ∈ s, f i) a) ^ q ∂μ) ^ (1 / q)) ^ q := by
                rw [one_div, ENNReal.rpow_inv_rpow hq_ne]
            _ ≤ (∑' i, A i) ^ q := ENNReal.rpow_le_rpow hs hq_pos.le
        exact h1.trans_le (h2.trans_le h3)
      have hLHS : eLpNorm (fun a => ∑' i, f i a) p μ
          = (∫⁻ a, (∑' i, f i a) ^ q ∂μ) ^ (1 / q) := by
        rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hp_ne_top
          (AEMeasurable.ennreal_tsum hf).aestronglyMeasurable]
        simp only [enorm_eq_self, ← hq_def]
      have hRHS : (∑' i, eLpNorm (f i) p μ) = ∑' i, A i := by
        refine tsum_congr (fun i => ?_)
        rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hp_ne_top (hf i).aestronglyMeasurable, hA]
        simp only [enorm_eq_self, ← hq_def]
      rw [hLHS, hRHS]
      calc (∫⁻ a, (∑' i, f i a) ^ q ∂μ) ^ (1 / q)
          ≤ ((∑' i, A i) ^ q) ^ (1 / q) :=
            ENNReal.rpow_le_rpow hmain (one_div_pos.mpr hq_pos).le
        _ = ∑' i, A i := by
            rw [one_div, ENNReal.rpow_rpow_inv hq_ne]

end Commons.MeasureTheory.Lp