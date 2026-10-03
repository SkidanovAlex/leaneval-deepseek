import Mathlib

/-!
# Fubini/Tonelli in the swapped direction for null-measurable sets

`MeasureTheory.Measure.prod_apply_symm` gives, for a *measurable* set `s`,

`μ.prod ν s = ∫⁻ y, μ {x | (x, y) ∈ s} ∂ν`.

Here we extend this to sets that are only `NullMeasurableSet` for the product measure, in
the same way that `prod_apply_null_measurable` extends `Measure.prod_apply`.  The section
`{x | (x, y) ∈ s}` need not be `μ`-measurable; its `μ`-measure is interpreted as an outer
measure and `MeasureTheory.measure_congr` makes the argument work.

The key auxiliary fact is `measure_ae_null_of_prod_null_symm`: the `ν`-a.e. statement
version of `Measure.measure_ae_null_of_prod_null`, obtained by transporting through
`Prod.swap`.
-/

open scoped symmDiff

namespace Work.FIArea3.JointCount

/-- If a set `s ⊆ α × β` has `(μ.prod ν)`-measure zero, then `ν`-a.e. of its
`y`-sections `{x | (x, y) ∈ s}` have `μ`-measure zero.  This is the swapped companion of
`MeasureTheory.Measure.measure_ae_null_of_prod_null`. -/
theorem measure_ae_null_of_prod_null_symm {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : MeasureTheory.Measure α} {ν : MeasureTheory.Measure β} [MeasureTheory.SFinite μ]
    [MeasureTheory.SFinite ν] {s : Set (α × β)} (h : μ.prod ν s = 0) :
    (fun y => μ {x | (x, y) ∈ s}) =ᵐ[ν] 0 := by
  have h' : ν.prod μ (Prod.swap ⁻¹' s) = 0 := by
    have key : ν.prod μ (Prod.swap ⁻¹' s) = (μ.prod ν) s := by
      rw [show ν.prod μ
            = (μ.prod ν).map (MeasurableEquiv.prodComm : α × β ≃ᵐ β × α) from
          MeasureTheory.Measure.prod_swap.symm]
      rw [MeasurableEquiv.map_apply]
      congr 1
    rw [key, h]
  have h2 := MeasureTheory.Measure.measure_ae_null_of_prod_null (μ := ν) (ν := μ) h'
  filter_upwards [h2] with y hy
  have hset : Prod.mk y ⁻¹' (Prod.swap ⁻¹' s) = {x | (x, y) ∈ s} := by
    ext x; simp [Prod.swap]
  rwa [hset] at hy

theorem prod_apply_symm_null_measurable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β] {μ : MeasureTheory.Measure α} {ν : MeasureTheory.Measure β} [MeasureTheory.SFinite ν] [MeasureTheory.SFinite μ] {s : Set (α × β)} (hs : MeasureTheory.NullMeasurableSet s (μ.prod ν)) : μ.prod ν s = ∫⁻ y, μ {x | (x, y) ∈ s} ∂ν := by
  -- Approximate `s` from above by a measurable set `t`, up to a `(μ.prod ν)`-null set.
  obtain ⟨t, _hsub, htm, hst⟩ := hs.exists_measurable_superset_ae_eq
  -- The two section-measure functions agree `ν`-a.e.
  have hfun : (fun y => μ {x | (x, y) ∈ t}) =ᵐ[ν] (fun y => μ {x | (x, y) ∈ s}) := by
    have hm : (μ.prod ν) (s ∆ t) = 0 := by
      rw [symmDiff_comm]
      exact (MeasureTheory.measure_symmDiff_eq_zero_iff).2 hst
    have hae : (fun y => μ ((fun x => (x, y)) ⁻¹' (s ∆ t))) =ᵐ[ν] 0 :=
      measure_ae_null_of_prod_null_symm hm
    filter_upwards [hae] with y hy
    rw [Set.preimage_symmDiff] at hy
    -- `ν`-a.e. equal sections have equal `μ`-measure (as outer measures).
    exact (MeasureTheory.measure_congr ((MeasureTheory.measure_symmDiff_eq_zero_iff).1 hy)).symm
  calc
    μ.prod ν s = μ.prod ν t := (MeasureTheory.measure_congr hst).symm
    _ = ∫⁻ y, μ {x | (x, y) ∈ t} ∂ν := MeasureTheory.Measure.prod_apply_symm htm
    _ = ∫⁻ y, μ {x | (x, y) ∈ s} ∂ν := MeasureTheory.lintegral_congr_ae hfun

end Work.FIArea3.JointCount
