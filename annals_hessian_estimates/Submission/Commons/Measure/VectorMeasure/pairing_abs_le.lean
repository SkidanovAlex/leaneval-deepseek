import Mathlib

namespace Commons.Measure.VectorMeasure

open MeasureTheory Metric Set Filter Function in
open scoped BigOperators ENNReal Topology Convolution in
theorem pairing_abs_le {X : Type*} [MeasurableSpace X] (ν : SignedMeasure X) (f : X → ℝ) :
    |(∫ᵛ x, f x ∂•ν : ℝ)| ≤ ∫ x, |f x| ∂ν.totalVariation := by
  have h := VectorMeasure.norm_integral_le_integral_norm
    (B := ContinuousLinearMap.lsmul ℝ ℝ) (f := f) (μ := ν)
  rw [Real.norm_eq_abs] at h
  rw [← SignedMeasure.totalVariation_eq_variation ν] at h
  simpa only [Real.norm_eq_abs, ContinuousLinearMap.opNorm_lsmul, one_mul] using h

end Commons.Measure.VectorMeasure
