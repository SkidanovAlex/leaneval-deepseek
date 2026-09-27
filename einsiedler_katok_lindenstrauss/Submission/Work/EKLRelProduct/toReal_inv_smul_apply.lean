import Mathlib

namespace Work.EKLRelProduct

theorem toReal_inv_smul_apply {α : Type*} [MeasurableSpace α] (μ : MeasureTheory.Measure α) (s t : Set α) :
    ((((μ s)⁻¹) • μ) t).toReal = (μ t).toReal / (μ s).toReal := by
  rw [MeasureTheory.Measure.smul_apply, smul_eq_mul, ENNReal.toReal_mul, ENNReal.toReal_inv,
    inv_mul_eq_div]

end Work.EKLRelProduct
