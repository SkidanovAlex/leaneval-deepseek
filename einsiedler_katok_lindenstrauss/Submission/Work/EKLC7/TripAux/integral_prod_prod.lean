import Mathlib

namespace Work.EKLC7.TripAux

theorem integral_prod_prod {α β γ E : Type*} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ] {μ : MeasureTheory.Measure α} {ν : MeasureTheory.Measure β} {ρ : MeasureTheory.Measure γ} [MeasureTheory.SFinite μ] [MeasureTheory.SFinite ν] [MeasureTheory.SFinite ρ] [NormedAddCommGroup E] [NormedSpace ℝ E] (f : α × β × γ → E) (hf : MeasureTheory.Integrable f (μ.prod (ν.prod ρ))) : ∫ x, f x ∂(μ.prod (ν.prod ρ)) = ∫ a, ∫ b, ∫ c, f (a, b, c) ∂ρ ∂ν ∂μ := by
  rw [MeasureTheory.integral_prod f hf]
  refine MeasureTheory.integral_congr_ae ?_
  filter_upwards [hf.prod_right_ae] with a ha
  exact MeasureTheory.integral_prod (fun y => f (a, y)) ha

end Work.EKLC7.TripAux
