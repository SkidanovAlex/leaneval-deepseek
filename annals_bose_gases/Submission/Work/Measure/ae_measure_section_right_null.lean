import Mathlib.MeasureTheory.Measure.Prod
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

open MeasureTheory

namespace Work.Measure

/-- If a measurable set `s ⊆ E × Y` is null for the product measure `μ.prod ν`, then for
`ν`-almost every `w`, the right section `{p | (p, w) ∈ s}` is `μ`-null. -/
lemma ae_measure_section_right_null {E Y : Type*} [MeasurableSpace E] [MeasurableSpace Y]
    (μ : MeasureTheory.Measure E) (ν : MeasureTheory.Measure Y)
    [MeasureTheory.SFinite μ] [MeasureTheory.SFinite ν]
    {s : Set (E × Y)} (hs : MeasurableSet s) (h : μ.prod ν s = 0) :
    ∀ᵐ w ∂ν, μ {p | (p, w) ∈ s} = 0 := by
  -- `w ↦ μ {p | (p, w) ∈ s}` is measurable (s-finiteness of `μ`),
  have hmeas : Measurable fun w : Y => μ {p | (p, w) ∈ s} :=
    measurable_measure_prodMk_right hs
  -- and its integral against `ν` is `μ.prod ν s = 0` by the symmetric version of Tonelli.
  rw [MeasureTheory.Measure.prod_apply_symm hs] at h
  have hae := (MeasureTheory.lintegral_eq_zero_iff hmeas).mp h
  filter_upwards [hae] with w hw
  simpa using hw

end Work.Measure
