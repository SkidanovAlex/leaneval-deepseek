import Mathlib.MeasureTheory.Integral.Prod
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SmallBoxSliding

theorem integrable_mul_prod_restrict {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : MeasureTheory.Measure α} {ν : MeasureTheory.Measure β} [MeasureTheory.SFinite μ]
    [MeasureTheory.SFinite ν] {s : Set α} {t : Set β} {f : α → ℝ} {g : β → ℝ}
    (hf : MeasureTheory.Integrable f μ) (hg : MeasureTheory.Integrable g ν) :
    MeasureTheory.Integrable (fun p : α × β => f p.1 * g p.2)
      ((μ.restrict s).prod (ν.restrict t)) := by
  have hf' : MeasureTheory.Integrable f (μ.restrict s) :=
    hf.mono_measure MeasureTheory.Measure.restrict_le_self
  have hg' : MeasureTheory.Integrable g (ν.restrict t) :=
    hg.mono_measure MeasureTheory.Measure.restrict_le_self
  exact hf'.mul_prod hg'

end Work.SmallBoxSliding
