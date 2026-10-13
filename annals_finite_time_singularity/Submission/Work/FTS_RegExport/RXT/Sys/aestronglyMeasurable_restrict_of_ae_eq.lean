import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable
import Mathlib.MeasureTheory.Measure.Haar.OfBasis

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_RegExport.RXT.Sys

theorem aestronglyMeasurable_restrict_of_ae_eq {F G : ℝ → ℝ} {s : Set ℝ} (hs : MeasurableSet s)
    (hG : Measurable G) (h : ∀ x ∈ s, F x = G x) :
    MeasureTheory.AEStronglyMeasurable F (MeasureTheory.volume.restrict s) := by
  have hG' : MeasureTheory.AEStronglyMeasurable G (MeasureTheory.volume.restrict s) :=
    hG.stronglyMeasurable.aestronglyMeasurable
  refine hG'.congr ?_
  filter_upwards [MeasureTheory.ae_restrict_mem hs] with x hx
  exact (h x hx).symm

end Work.FTS_RegExport.RXT.Sys
