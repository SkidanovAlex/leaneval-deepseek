import Mathlib

open MeasureTheory

namespace Work.EKLC7

/-- For a measure which is finite on compacts and a nonnegative compactly supported continuous
function `f`, the Lebesgue integral `∫⁻ x, ofReal (f x) ∂ν` is finite and coincides with
`ofReal (∫ x, f x ∂ν)`.

The finiteness is `Integrable.lintegral_lt_top` applied to the fact that a compactly supported
continuous function is integrable for a measure finite on compacts, and the identity is
`ofReal_integral_eq_lintegral_ofReal`. -/
theorem lintegral_ofReal_lt_top_of_integrable {X : Type*} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X] (ν : MeasureTheory.Measure X) [MeasureTheory.IsFiniteMeasureOnCompacts ν] (f : CompactlySupportedContinuousMap X ℝ) (hf0 : ∀ x, 0 ≤ f x) : (∫⁻ x, ENNReal.ofReal (f x) ∂ν) < ⊤ ∧ (∫⁻ x, ENNReal.ofReal (f x) ∂ν) = ENNReal.ofReal (∫ x, f x ∂ν) := by
  have hI : Integrable f ν := CompactlySupportedContinuousMap.integrable f
  exact ⟨Integrable.lintegral_lt_top hI,
    (ofReal_integral_eq_lintegral_ofReal hI (Filter.Eventually.of_forall hf0)).symm⟩

end Work.EKLC7
