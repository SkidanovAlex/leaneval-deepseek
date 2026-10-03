import Mathlib

/-!
# Slices of an `AEMeasurable` function on `ℝ × ℤ` against `volume × count`

If `(t, x) ↦ X t n x` is almost everywhere measurable for the product of Lebesgue measure on `ℝ`
and counting measure on `ℤ`, then each *slice* `t ↦ X t n x` (at a fixed `x : ℤ`) is almost
everywhere measurable for Lebesgue measure.  The point is that "almost everywhere" for the
counting measure means "everywhere" (`MeasureTheory.Measure.ae_count_iff`), so the a.e.-currying
lemma `MeasureTheory.Measure.ae_ae_eq_curry_of_prod` gives control of *every* slice at once.
-/

namespace Work.KMTAreas.A7

open MeasureTheory

lemma aemeasurable_slice_prod_count {X : ℝ → ℕ → ℤ → ℂ} (n : ℕ)
    (hX : AEMeasurable (fun p : ℝ × ℤ => X p.1 n p.2)
      (MeasureTheory.volume.prod MeasureTheory.Measure.count)) :
    ∀ x : ℤ, AEMeasurable (fun t : ℝ => X t n x) MeasureTheory.volume := by
  -- `hX` provides a measurable representative `g` of the joint function.
  obtain ⟨g, hg, hfg⟩ := hX
  -- Since `fst` is a.e.-measurable, the curried family of `snd`-slices is a.e. equal to that of
  -- `g`; for the counting measure, `=ᵐ[count]` is actual equality.
  have hae : ∀ᵐ t ∂MeasureTheory.volume,
      (fun y : ℤ => X t n y) =ᵐ[MeasureTheory.Measure.count] (fun y : ℤ => g (t, y)) :=
    MeasureTheory.Measure.ae_ae_eq_curry_of_prod hfg
  intro x
  refine ⟨fun t => g (t, x), hg.comp ?_, ?_⟩
  · exact Measurable.prodMk measurable_id measurable_const
  · filter_upwards [hae] with t ht
    exact MeasureTheory.Measure.ae_count_iff.mp ht x

end Work.KMTAreas.A7
