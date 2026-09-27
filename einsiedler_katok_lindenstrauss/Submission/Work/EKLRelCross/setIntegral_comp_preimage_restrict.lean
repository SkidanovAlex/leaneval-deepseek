import Mathlib

namespace Work.EKLRelCross

/-- Change of variables for a measure-preserving `T`, restricted to the preimage of `Z`:
integrating `φ ∘ T` over `T ⁻¹' B` against `μ.restrict (T ⁻¹' Z)` is the same as
integrating `φ` over `B` against `μ.restrict Z`.

The proof combines `Measure.restrict_map` (the restriction of the pushforward is the
pushforward of the restriction) with `MeasurePreserving.map_eq` to identify
`(μ.restrict (T ⁻¹' Z)).map T = μ.restrict Z`, and then applies the change-of-variables
formula `MeasureTheory.setIntegral_map`. -/
theorem setIntegral_comp_preimage_restrict
    {α : Type*} [mX : MeasurableSpace α] (T : α → α) (μ : MeasureTheory.Measure α)
    [MeasureTheory.IsFiniteMeasure μ]
    (hT : MeasureTheory.MeasurePreserving T μ μ)
    {Z B : Set α} (hZ : MeasurableSet Z) (hB : MeasurableSet B)
    {φ : α → ℝ} (hint : MeasureTheory.Integrable φ (μ.restrict Z)) :
    ∫ x in T ⁻¹' B, φ (T x) ∂(μ.restrict (T ⁻¹' Z)) = ∫ x in B, φ x ∂(μ.restrict Z) := by
  have hmap : MeasureTheory.Measure.map T (μ.restrict (T ⁻¹' Z)) = μ.restrict Z := by
    rw [← MeasureTheory.Measure.restrict_map hT.measurable hZ, hT.map_eq]
  have hf : MeasureTheory.AEStronglyMeasurable φ
      (MeasureTheory.Measure.map T (μ.restrict (T ⁻¹' Z))) := by
    rw [hmap]
    exact hint.aestronglyMeasurable
  rw [← hmap, MeasureTheory.setIntegral_map hB hf hT.measurable.aemeasurable]

end Work.EKLRelCross
