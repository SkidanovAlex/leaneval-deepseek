import Mathlib
import Submission.Work.EKLComp.C8Defs

namespace Work.EKLCompSetup

open MeasureTheory

/-- For a probability measure `μ`, the integral of `1 - 1_S` is `1 - (μ S).toReal`. -/
theorem integral_one_sub_indicator
    {α : Type*} [MeasurableSpace α] (μ : MeasureTheory.Measure α)
    [MeasureTheory.IsProbabilityMeasure μ] (S : Set α) (hS : MeasurableSet S) :
    ∫ x, (1 - Set.indicator S (fun _ => (1 : ℝ)) x) ∂μ = 1 - (μ S).toReal := by
  have hconst_int : MeasureTheory.Integrable (fun _ : α => (1 : ℝ)) μ :=
    MeasureTheory.integrable_const 1
  have hInd_int : MeasureTheory.Integrable (Set.indicator S (fun _ => (1 : ℝ))) μ := by
    apply MeasureTheory.Integrable.of_bound (C := 1)
    · exact ((measurable_const : Measurable (fun _ : α => (1 : ℝ))).indicator hS).aestronglyMeasurable
    · filter_upwards with x
      rw [Real.norm_eq_abs]
      by_cases hx : x ∈ S <;> simp [Set.indicator_of_mem, Set.indicator_of_notMem, hx]
  rw [MeasureTheory.integral_sub hconst_int hInd_int]
  rw [MeasureTheory.integral_const, MeasureTheory.integral_indicator hS,
    MeasureTheory.setIntegral_const]
  simp only [MeasureTheory.Measure.real, MeasureTheory.measure_univ, ENNReal.toReal_one,
    smul_eq_mul, mul_one]

theorem measure_bad_le
    {μ : MeasureTheory.Measure Work.EKLContract.X3} [MeasureTheory.IsProbabilityMeasure μ]
    {S : Set Work.EKLContract.X3} (hS : MeasurableSet S)
    {C ε : ℝ} (hC : 0 < C) (hε : 0 < ε) (hSmeas : 1 - C * ε ^ 2 ≤ (μ S).toReal)
    (hMF : ∀ (f : Work.EKLContract.X3 → ℝ), Measurable f → (∀ x, 0 ≤ f x) →
      MeasureTheory.Integrable f μ →
      ∀ α : ℝ, 0 < α →
        μ {x | ∃ T : ℝ, 0 < T ∧
            α * T < ∫ τ in (0 : ℝ)..T, f (Work.EKLComp.Phi τ x)}
          ≤ ENNReal.ofReal ((∫ x, f x ∂μ) / α)) :
    μ {x | ∃ T : ℝ, 0 < T ∧
        ε * T < ∫ τ in (0 : ℝ)..T,
          (1 - Set.indicator S (fun _ => (1 : ℝ)) (Work.EKLComp.Phi τ x))}
      ≤ ENNReal.ofReal (C * ε) := by
  have hf_meas : Measurable
      (fun x : Work.EKLContract.X3 => 1 - Set.indicator S (fun _ => (1 : ℝ)) x) :=
    measurable_const.sub (measurable_const.indicator hS)
  have hf_nonneg : ∀ x : Work.EKLContract.X3,
      0 ≤ 1 - Set.indicator S (fun _ => (1 : ℝ)) x := by
    intro x
    by_cases hx : x ∈ S <;> simp [Set.indicator_of_mem, Set.indicator_of_notMem, hx]
  have hf_int : MeasureTheory.Integrable
      (fun x : Work.EKLContract.X3 => 1 - Set.indicator S (fun _ => (1 : ℝ)) x) μ := by
    apply MeasureTheory.Integrable.of_bound (C := 1)
    · exact hf_meas.aestronglyMeasurable
    · filter_upwards with x
      rw [Real.norm_eq_abs]
      by_cases hx : x ∈ S <;> simp [Set.indicator_of_mem, Set.indicator_of_notMem, hx]
  refine le_trans (hMF (fun x : Work.EKLContract.X3 => 1 - Set.indicator S (fun _ => (1 : ℝ)) x)
    hf_meas hf_nonneg hf_int ε hε) ?_
  change ENNReal.ofReal ((∫ x, (1 - Set.indicator S (fun _ => (1 : ℝ)) x) ∂μ) / ε)
    ≤ ENNReal.ofReal (C * ε)
  apply ENNReal.ofReal_le_ofReal
  rw [integral_one_sub_indicator μ S hS, div_le_iff₀ hε]
  nlinarith [hSmeas]

end Work.EKLCompSetup
