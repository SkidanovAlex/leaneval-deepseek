import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Integral.MeanInequalities

open MeasureTheory ENNReal
open scoped ENNReal

namespace Commons.MeasureTheory.Lp

variable {α ι : Type*}

/-- Minkowski's inequality (finite form) for `ℝ≥0∞`-valued functions:
`(∫ (∑_{i ∈ s} fᵢ)^q)^{1/q} ≤ ∑_{i ∈ s} (∫ fᵢ^q)^{1/q}` for `q ≥ 1`. -/
private lemma finset_lintegral_rpow_sum_le {m : MeasurableSpace α} {μ : Measure α}
    {q : ℝ} (hq : 1 ≤ q) {f : ι → α → ℝ≥0∞} {s : Finset ι}
    (hf : ∀ i ∈ s, AEMeasurable (f i) μ) :
    (∫⁻ x, (∑ i ∈ s, f i x) ^ q ∂μ) ^ (1 / q) ≤
      ∑ i ∈ s, (∫⁻ x, (f i x) ^ q ∂μ) ^ (1 / q) := by
  classical
  induction s using Finset.induction with
  | empty =>
      have hq_pos : (0 : ℝ) < q := lt_of_lt_of_le zero_lt_one hq
      have hq1_pos : (0 : ℝ) < 1 / q := div_pos one_pos hq_pos
      have hzero : (∫⁻ x, (∑ i ∈ ∅, f i x) ^ q ∂μ) = 0 := by
        simp only [Finset.sum_empty]
        rw [ENNReal.zero_rpow_of_pos hq_pos, lintegral_zero]
      rw [hzero, Finset.sum_empty, ENNReal.zero_rpow_of_pos hq1_pos]
  | insert a s ha ih =>
      have hq_pos : (0 : ℝ) < q := lt_of_lt_of_le zero_lt_one hq
      have hfa : AEMeasurable (f a) μ := hf a (Finset.mem_insert_self a s)
      have hfs : ∀ i ∈ s, AEMeasurable (f i) μ :=
        fun i hi => hf i (Finset.mem_insert_of_mem hi)
      have hG : AEMeasurable (fun x => ∑ i ∈ s, f i x) μ :=
        Finset.aemeasurable_fun_sum s hfs
      simp only [Finset.sum_insert ha]
      refine (ENNReal.lintegral_Lp_add_le hfa hG hq).trans ?_
      exact add_le_add le_rfl (ih hfs)

theorem eLpNorm_finset_sum_le_ennreal {α ι : Type*} {m : MeasurableSpace α} {μ : MeasureTheory.Measure α}
    {p : ENNReal} (hp : 1 ≤ p) {s : Finset ι} {g : ι → α → ENNReal}
    (hg : ∀ i ∈ s, AEMeasurable (g i) μ) :
    MeasureTheory.eLpNorm (fun a => ∑ i ∈ s, g i a) p μ
      ≤ ∑ i ∈ s, MeasureTheory.eLpNorm (g i) p μ := by
  classical
  have hsum : AEStronglyMeasurable (fun a => ∑ i ∈ s, g i a) μ :=
    (Finset.aemeasurable_fun_sum s hg).aestronglyMeasurable
  rcases eq_or_ne p ⊤ with rfl | hp_top
  · rw [eLpNorm_exponent_top hsum]
    refine eLpNormEssSup_le_of_ae_enorm_bound ?_
    have hkey : ∀ᵐ x ∂μ, ∀ i ∈ s, g i x ≤ eLpNorm (g i) ∞ μ := by
      rw [Filter.eventually_all_finset]
      intro i hi
      filter_upwards [ae_le_eLpNormEssSup (f := g i) (μ := μ)] with x hx
      rw [eLpNorm_exponent_top (hg i hi).aestronglyMeasurable]
      simpa [enorm_eq_self] using hx
    filter_upwards [hkey] with x hx
    simp only [enorm_eq_self]
    exact Finset.sum_le_sum fun i hi => hx i hi
  · rcases eq_or_ne p 0 with rfl | hp0
    · exact absurd hp (by simp)
    · set q : ℝ := p.toReal with hq_def
      have hq1 : 1 ≤ q := by
        rw [hq_def]
        simpa using ENNReal.toReal_mono hp_top hp
      have hLHS : eLpNorm (fun a => ∑ i ∈ s, g i a) p μ
          = (∫⁻ a, (∑ i ∈ s, g i a) ^ q ∂μ) ^ (1 / q) := by
        rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hp_top hsum]
        simp only [enorm_eq_self, ← hq_def]
      have hRHS : (∑ i ∈ s, eLpNorm (g i) p μ)
          = ∑ i ∈ s, (∫⁻ a, (g i a) ^ q ∂μ) ^ (1 / q) := by
        refine Finset.sum_congr rfl (fun i hi => ?_)
        rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hp_top (hg i hi).aestronglyMeasurable]
        simp only [enorm_eq_self, ← hq_def]
      rw [hLHS, hRHS]
      exact finset_lintegral_rpow_sum_le hq1 hg

end Commons.MeasureTheory.Lp