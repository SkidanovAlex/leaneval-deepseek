import Mathlib

namespace Work.EKLRelProduct

open MeasureTheory

theorem toReal_inv_smul_restrict_apply {α : Type*} [MeasurableSpace α] (μ : MeasureTheory.Measure α)
    {s : Set α} (hs : MeasurableSet s) (t : Set α) :
    ((((μ s)⁻¹) • μ.restrict s) t).toReal = (μ (t ∩ s)).toReal / (μ s).toReal := by
  rw [Measure.smul_apply, smul_eq_mul, Measure.restrict_apply' hs, ENNReal.toReal_mul,
    ENNReal.toReal_inv, div_eq_mul_inv, mul_comm]

end Work.EKLRelProduct
