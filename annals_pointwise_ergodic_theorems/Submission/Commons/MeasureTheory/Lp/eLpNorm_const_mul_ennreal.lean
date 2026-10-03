import Mathlib.MeasureTheory.Function.LpSeminorm.Basic

namespace Commons.MeasureTheory.Lp

open scoped ENNReal NNReal

/-- The `ℒᵖ` seminorm of an `ℝ≥0∞`-valued function is homogeneous under multiplication by a
finite constant `c ≠ ⊤`, for `0 < p < ∞`. -/
theorem eLpNorm_const_mul_ennreal {α : Type*} [MeasurableSpace α] {μ : MeasureTheory.Measure α}
    {V : α → ENNReal} {c : ENNReal} (hc : c ≠ ⊤) {p : ENNReal} (hp0 : p ≠ 0) (hp : p ≠ ⊤) :
    MeasureTheory.eLpNorm (fun x => c * V x) p μ = c * MeasureTheory.eLpNorm V p μ := by
  by_cases hc0 : c = 0
  · subst hc0; simpa using (MeasureTheory.eLpNorm_zero (α := α) (ε := ℝ≥0∞) (p := p) (μ := μ))
  by_cases hV : MeasureTheory.AEStronglyMeasurable V μ
  swap
  · have hcV : ¬ MeasureTheory.AEStronglyMeasurable (fun x => c * V x) μ := by
      intro h
      apply hV
      have h2 := (h.aemeasurable.const_mul c⁻¹).aestronglyMeasurable
      refine h2.congr (Filter.Eventually.of_forall fun x => ?_)
      simp only
      rw [← mul_assoc, ENNReal.inv_mul_cancel hc0 hc, one_mul]
    rw [MeasureTheory.eLpNorm_of_not_aestronglyMeasurable hV,
      MeasureTheory.eLpNorm_of_not_aestronglyMeasurable hcV, ENNReal.mul_top hc0]
  have hcV : MeasureTheory.AEStronglyMeasurable (fun x => c * V x) μ :=
    (hV.aemeasurable.const_mul c).aestronglyMeasurable
  rw [MeasureTheory.eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hp hcV,
      MeasureTheory.eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hp hV]
  have hr : 0 ≤ p.toReal := ENNReal.toReal_nonneg
  have hrpos : 0 < p.toReal := ENNReal.toReal_pos hp0 hp
  have hcr : c ^ p.toReal ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg hr hc
  have h1r : (0:ℝ) ≤ 1 / p.toReal := by positivity
  simp only [enorm_eq_self]
  rw [MeasureTheory.lintegral_congr fun x => ENNReal.mul_rpow_of_nonneg c (V x) hr]
  rw [MeasureTheory.lintegral_const_mul' (c ^ p.toReal) (fun x => V x ^ p.toReal) hcr]
  rw [ENNReal.mul_rpow_of_nonneg (c ^ p.toReal) _ h1r]
  rw [one_div, ENNReal.rpow_rpow_inv hrpos.ne' c]

end Commons.MeasureTheory.Lp