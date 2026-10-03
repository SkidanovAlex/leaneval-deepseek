import Mathlib

/-!
# Almost everywhere measurability for `volume × count` on `ℝ × ℤ`

For a function `F : ℝ → ℤ → ℂ`, joint a.e.-measurability of `(t, x) ↦ F t x` for the product of
Lebesgue measure on `ℝ` and counting measure on `ℤ` is equivalent to a.e.-measurability of every
*slice* `t ↦ F t x`.

This is the (bi-directional) statement used when interchanging a `t`-integral with a `ℤ`-sum via
Tonelli in the small-scale analysis of area A6.  Both directions are specific to the counting
measure on the countable type `ℤ`:

* (⇐) countably many a.e.-equal representatives of the slices glue to a single measurable function
  of `(t, x)` (`measurable_from_prod_countable_left`, which uses that `ℤ` is countable with
  measurable singletons), and the union of the countably many null sets is null;
* (⇒) for the counting measure "a.e." means "everywhere" (`Measure.ae_count_iff`), so the a.e.
  currying lemma `Measure.ae_ae_of_ae_prod` controls *every* slice at once.
-/

namespace Work.KMTPlan.A6

open MeasureTheory

theorem aemeasurable_prod_count_iff (F : ℝ → ℤ → ℂ) :
    AEMeasurable (Function.uncurry F) (MeasureTheory.Measure.prod MeasureTheory.volume MeasureTheory.Measure.count)
      ↔ ∀ x : ℤ, AEMeasurable (fun t : ℝ => F t x) MeasureTheory.volume := by
  constructor
  · -- (⇒) take a measurable representative of the joint function; its slices witness the claim.
    intro h
    obtain ⟨H, hHmeas, hHae⟩ := h
    have key : ∀ᵐ t ∂(MeasureTheory.volume : Measure ℝ),
        ∀ᵐ x ∂(MeasureTheory.Measure.count : Measure ℤ),
          Function.uncurry F (t, x) = H (t, x) :=
      Measure.ae_ae_of_ae_prod hHae
    intro x
    refine ⟨fun t : ℝ => H (t, x), hHmeas.comp measurable_prodMk_right, ?_⟩
    filter_upwards [key] with t ht
    exact Measure.ae_count_iff.mp ht x
  · -- (⇐) glue the countably many slice representatives into one measurable function.
    intro h
    let g : ℤ → ℝ → ℂ := fun x => (h x).mk (fun t : ℝ => F t x)
    have hgmeas : ∀ x : ℤ, Measurable (g x) := fun x => (h x).measurable_mk
    have hgae : ∀ x : ℤ, (fun t : ℝ => F t x) =ᵐ[(MeasureTheory.volume : Measure ℝ)] g x :=
      fun x => (h x).ae_eq_mk
    have hfmeas : Measurable (fun p : ℝ × ℤ => g p.2 p.1) :=
      measurable_from_prod_countable_left (f := fun p : ℝ × ℤ => g p.2 p.1) fun y => hgmeas y
    have hae : Function.uncurry F
        =ᵐ[MeasureTheory.Measure.prod MeasureTheory.volume MeasureTheory.Measure.count]
          (fun p : ℝ × ℤ => g p.2 p.1) := by
      refine MeasureTheory.ae_iff.2 ?_
      have hsub : {a : ℝ × ℤ | ¬ Function.uncurry F a = (fun p : ℝ × ℤ => g p.2 p.1) a}
          ⊆ ⋃ y : ℤ, {t : ℝ | F t y ≠ g y t} ×ˢ ({y} : Set ℤ) := by
        intro p hp
        exact Set.mem_iUnion.mpr ⟨p.2, ⟨hp, rfl⟩⟩
      have hnull : (MeasureTheory.Measure.prod MeasureTheory.volume MeasureTheory.Measure.count)
          (⋃ y : ℤ, {t : ℝ | F t y ≠ g y t} ×ˢ ({y} : Set ℤ)) = 0 := by
        rw [measure_iUnion_null_iff]
        intro y
        have hAy : (MeasureTheory.volume : Measure ℝ) {t : ℝ | F t y ≠ g y t} = 0 := by
          rw [← MeasureTheory.ae_iff]
          exact hgae y
        have hle := Measure.prod_prod_le (μ := (MeasureTheory.volume : Measure ℝ))
          (ν := (MeasureTheory.Measure.count : Measure ℤ))
          {t : ℝ | F t y ≠ g y t} ({y} : Set ℤ)
        rw [hAy, zero_mul] at hle
        exact le_antisymm hle zero_le
      exact measure_mono_null hsub hnull
    exact (hfmeas.aemeasurable).congr hae.symm

end Work.KMTPlan.A6
