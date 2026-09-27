import Mathlib
import Submission.Work.EKLComp.Misiurewicz.Defs

namespace Work.Misiurewicz

open MeasureTheory Filter
open Work.EKLComp Work.EKLContract
open scoped ENNReal

/-- Integrability against a finite sum of measures. -/
lemma integrable_finset_sum_measure {ι : Type*} (f : X3 → ℝ) :
    ∀ (s : Finset ι) (μ : ι → Measure X3), (∀ i ∈ s, Integrable f (μ i)) →
      Integrable f (∑ i ∈ s, μ i) := by
  classical
  intro s
  induction s using Finset.induction_on with
  | empty => intro μ _; simp
  | insert a s ha ih =>
      intro μ h
      rw [Finset.sum_insert ha]
      exact (h a (Finset.mem_insert_self a s)).add_measure
        (ih μ fun i hi => h i (Finset.mem_insert_of_mem hi))

/-- Integrating against a finite sum of measures is the same as summing the integrals.
Mathlib has this only for `Measure.sum`, not for `Finset.sum`, so we prove it by induction. -/
lemma integral_finset_sum_measure {ι : Type*} (f : X3 → ℝ) :
    ∀ (s : Finset ι) (μ : ι → Measure X3), (∀ i ∈ s, Integrable f (μ i)) →
      ∫ x, f x ∂(∑ i ∈ s, μ i) = ∑ i ∈ s, ∫ x, f x ∂μ i := by
  classical
  intro s
  induction s using Finset.induction_on with
  | empty => intro μ _; simp
  | insert a s ha ih =>
      intro μ h
      rw [Finset.sum_insert ha, Finset.sum_insert ha,
        integral_add_measure (h a (Finset.mem_insert_self a s))
          (integrable_finset_sum_measure f s μ fun i hi => h i (Finset.mem_insert_of_mem hi)),
        ih μ fun i hi => h i (Finset.mem_insert_of_mem hi)]

theorem integral_misAvg_diff_le (g : Work.EKLContract.SL3) {N : ℕ} (hN : 0 < N)
    (σ : MeasureTheory.Measure Work.EKLContract.X3) [MeasureTheory.IsProbabilityMeasure σ]
    (f : BoundedContinuousFunction Work.EKLContract.X3 ℝ) :
    |(∫ x, f x ∂MeasureTheory.Measure.map (Work.EKLComp.smulMap g) (Work.EKLComp.misAvgMeasure g N σ)) -
        (∫ x, f x ∂Work.EKLComp.misAvgMeasure g N σ)| ≤ 2 * ‖f‖ / N := by
  set c : ℝ := ((N : ℝ≥0∞)⁻¹).toReal with hcdef
  set b : ℕ → ℝ := fun k => ∫ x, f x ∂Measure.map (smulMap (g ^ k)) σ with hbdef
  have hc : c = (N : ℝ)⁻¹ := by rw [hcdef, ENNReal.toReal_inv, ENNReal.toReal_natCast]
  have hcnonneg : 0 ≤ c := by rw [hc]; positivity
  have hint : ∀ k : ℕ, Integrable (fun x => f x) (Measure.map (smulMap (g ^ k)) σ) := fun k =>
    Integrable.of_bound f.continuous.measurable.aestronglyMeasurable ‖f‖
      (Eventually.of_forall fun x => BoundedContinuousFunction.norm_coe_le_norm f x)
  -- Integral against the Misiurewicz average.
  have hB : ∫ x, f x ∂misAvgMeasure g N σ = c * ∑ k ∈ Finset.range N, b k := by
    rw [misAvgMeasure, integral_smul_measure, smul_eq_mul]
    congr 1
    rw [integral_finset_sum_measure (fun x => f x) (Finset.range N)
      (fun k => Measure.map (smulMap (g ^ k)) σ) (fun k _ => hint k)]
  -- The pushforward measure is the average of the shifted iterates.
  have hmap : Measure.map (smulMap g) (misAvgMeasure g N σ)
      = (N : ℝ≥0∞)⁻¹ • ∑ k ∈ Finset.range N, Measure.map (smulMap (g ^ (k + 1))) σ := by
    rw [misAvgMeasure, Measure.map_smul _ (continuous_smulMap _).measurable.aemeasurable]
    congr 1
    rw [Measure.map_finset_sum (continuous_smulMap g).measurable.aemeasurable]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Measure.map_map (continuous_smulMap g).measurable (continuous_smulMap (g ^ k)).measurable]
    congr 1
    funext x
    simp only [Function.comp_apply, smulMap_apply]
    rw [pow_succ', mul_smul]
  -- Integral against the pushforward of the Misiurewicz average.
  have hA : ∫ x, f x ∂Measure.map (smulMap g) (misAvgMeasure g N σ)
      = c * ∑ k ∈ Finset.range N, b (k + 1) := by
    rw [hmap, integral_smul_measure, smul_eq_mul]
    congr 1
    rw [integral_finset_sum_measure (fun x => f x) (Finset.range N)
      (fun k => Measure.map (smulMap (g ^ (k + 1))) σ) (fun k _ => hint (k + 1))]
  -- Telescoping.
  have htel : (∑ k ∈ Finset.range N, b (k + 1)) - (∑ k ∈ Finset.range N, b k) = b N - b 0 := by
    have h1 := Finset.sum_range_succ' b N
    have h2 := Finset.sum_range_succ b N
    linarith
  -- Uniform bound on each term.
  have hbnd : ∀ k, |b k| ≤ ‖f‖ := by
    intro k
    have hprob : (Measure.map (smulMap (g ^ k)) σ).real Set.univ = 1 := by
      rw [Measure.real, Measure.map_apply (continuous_smulMap (g ^ k)).measurable MeasurableSet.univ,
        Set.preimage_univ, IsProbabilityMeasure.measure_univ, ENNReal.toReal_one]
    rw [hbdef, ← Real.norm_eq_abs]
    refine (norm_integral_le_of_norm_le_const (f := fun x => f x) (C := ‖f‖)
      (Eventually.of_forall fun x => BoundedContinuousFunction.norm_coe_le_norm f x)).trans_eq ?_
    rw [hprob, mul_one]
  rw [hA, hB]
  have hdiff : c * (∑ k ∈ Finset.range N, b (k + 1)) - c * (∑ k ∈ Finset.range N, b k)
      = c * (b N - b 0) := by rw [← mul_sub, htel]
  rw [hdiff, abs_mul, abs_of_nonneg hcnonneg]
  calc c * |b N - b 0| ≤ c * (2 * ‖f‖) := by
        refine mul_le_mul_of_nonneg_left ?_ hcnonneg
        calc |b N - b 0| ≤ |b N| + |b 0| := abs_sub _ _
          _ ≤ ‖f‖ + ‖f‖ := add_le_add (hbnd N) (hbnd 0)
          _ = 2 * ‖f‖ := by ring
    _ = 2 * ‖f‖ / N := by rw [hc, div_eq_inv_mul]

end Work.Misiurewicz
