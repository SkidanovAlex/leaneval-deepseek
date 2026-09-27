import Mathlib

namespace Work.Mostow

/-- Push-forward of a measure with a density: if `map e μ = ν`, then pushing forward
`μ.withDensity (f ∘ e)` along `e` gives `ν.withDensity f`. -/
theorem map_withDensity_of_map_eq {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : MeasureTheory.Measure α} {ν : MeasureTheory.Measure β} {e : α → β} (he : Measurable e)
    (h : MeasureTheory.Measure.map e μ = ν) {f : β → ENNReal} (hf : Measurable f) :
    MeasureTheory.Measure.map e (μ.withDensity (f ∘ e)) = ν.withDensity f := by
  rw [← h]
  ext s hs
  rw [MeasureTheory.Measure.map_apply he hs]
  rw [MeasureTheory.withDensity_apply (f ∘ e) (he hs)]
  rw [MeasureTheory.withDensity_apply f hs]
  rw [← MeasureTheory.lintegral_indicator (μ := MeasureTheory.Measure.map e μ) hs f]
  rw [MeasureTheory.lintegral_map (hf.indicator hs) he]
  rw [← MeasureTheory.lintegral_indicator (μ := μ) (he hs) (f ∘ e)]
  refine MeasureTheory.lintegral_congr fun x => ?_
  by_cases hx : e x ∈ s <;> simp [Set.mem_preimage, hx]

end Work.Mostow
