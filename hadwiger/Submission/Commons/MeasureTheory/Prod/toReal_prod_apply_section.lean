import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic

namespace Commons.MeasureTheory.Prod

theorem toReal_prod_apply_section {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : MeasureTheory.Measure α} {ν : MeasureTheory.Measure β} [MeasureTheory.SFinite ν]
    {T : Set (α × β)} (hT : MeasurableSet T) (hfin : (μ.prod ν) T ≠ ⊤) :
    ((μ.prod ν) T).toReal = ∫ a, (ν (Prod.mk a ⁻¹' T)).toReal ∂μ := by
  rw [MeasureTheory.Measure.prod_apply hT]
  exact (MeasureTheory.integral_toReal
    (measurable_measure_prodMk_left hT).aemeasurable
    (MeasureTheory.Measure.ae_measure_lt_top hT hfin)).symm

end Commons.MeasureTheory.Prod