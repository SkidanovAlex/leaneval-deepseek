import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic

open MeasureTheory

namespace Commons.Measure.Markov

/-- Markov's inequality for the real part of a finite measure and the Bochner integral
of a nonnegative (a.e.) real-valued function. -/
theorem measureReal_markov {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsFiniteMeasure μ]
    {f : α → ℝ} (hf0 : 0 ≤ᵐ[μ] f) (hfi : Integrable f μ) (a : ℝ) (ha : 0 < a) :
    a * μ.real {x : α | a ≤ f x} ≤ ∫ x, f x ∂μ := by
  exact MeasureTheory.mul_meas_ge_le_integral_of_nonneg hf0 hfi a

end Commons.Measure.Markov