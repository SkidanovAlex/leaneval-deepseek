import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.MeasureTheory.VectorMeasure.Integral

namespace Commons.Measure.VectorMeasure

open MeasureTheory in
open scoped ENNReal in
theorem integral_toSignedMeasure_smul {α : Type*} [MeasurableSpace α] (μ : Measure α)
    [IsFiniteMeasure μ] (φ : α → ℝ) :
    ∫ᵛ x, φ x ∂•(μ.toSignedMeasure) = ∫ x, φ x ∂μ := by
  have hB : (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] ℝ →L[ℝ] ℝ)
      = (ContinuousLinearMap.lsmul ℝ ℝ).flip := by
    ext c x
    simp [ContinuousLinearMap.lsmul_apply]
  rw [hB]
  exact VectorMeasure.integral_toSignedMeasure

end Commons.Measure.VectorMeasure