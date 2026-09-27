import Mathlib

namespace Work.Mostow

/-- If `φ` preserves the measure `μ` (i.e. `μ.map φ = μ`) and `φ` is measurable, then for any
`AEStronglyMeasurable` map `f` into a normed space, the Bochner integral of `f ∘ φ` equals that
of `f`. -/
theorem integral_comp_eq_of_map_eq {α : Type*} [MeasurableSpace α] {μ : MeasureTheory.Measure α}
    {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    {φ : α → α} (hφ : Measurable φ) (h : μ.map φ = μ) (f : α → G)
    (hf : MeasureTheory.AEStronglyMeasurable f μ) :
    ∫ x, f (φ x) ∂μ = ∫ x, f x ∂μ := by
  have hmap : ∫ y, f y ∂(μ.map φ) = ∫ x, f (φ x) ∂μ :=
    MeasureTheory.integral_map (μ := μ) (φ := φ) hφ.aemeasurable (by rw [h]; exact hf)
  rw [h] at hmap
  exact hmap.symm

end Work.Mostow
