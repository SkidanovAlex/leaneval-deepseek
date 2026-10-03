import Mathlib

/-!
# Translation invariance of the `ℓ^p` norm on `ℤ`

For the counting measure on `ℤ` and any `X : ℤ → ℂ`, `p : ℝ≥0∞`, `t : ℤ`,

`‖X(· + t)‖_{ℓ^p(ℤ)} = ‖X‖_{ℓ^p(ℤ)}`.

The counting measure is invariant under the translation `x ↦ x + t` (a bijection of `ℤ`),
so this is the measure-preserving-change-of-variables statement `eLpNorm_comp_measurePreserving`.
The invariance of `count` is proved from `Measure.count_injective_image`: the preimage of a set
under `x ↦ x + t` equals its image under the inverse translation `y ↦ y - t`, and an injective map
preserves the counting measure.  No measurability of `X` is needed because `ℤ` is countable and
`MeasurableSingletonClass`, hence `DiscreteMeasurableSpace`.
-/

namespace Work.KMTAreas.A4Z

open MeasureTheory

theorem eLpNorm_comp_add_count (X : ℤ → ℂ) (p : ENNReal) (t : ℤ) :
    MeasureTheory.eLpNorm (fun x : ℤ => X (x + t)) p MeasureTheory.Measure.count
      = MeasureTheory.eLpNorm X p MeasureTheory.Measure.count := by
  -- The counting measure on `ℤ` is invariant under the translation `x ↦ x + t`.
  have hmap : Measure.map (fun x : ℤ => x + t) Measure.count = Measure.count := by
    ext s hs
    rw [Measure.map_apply (Measurable.of_discrete) hs]
    -- `{x | x + t ∈ s}` is the image of `s` under the inverse translation `y ↦ y - t`.
    have hpre : (fun x : ℤ => x + t) ⁻¹' s = (fun y : ℤ => y - t) '' s := by
      ext x
      simp only [Set.mem_preimage, Set.mem_image]
      constructor
      · intro hx; exact ⟨x + t, hx, by ring⟩
      · rintro ⟨y, hy, rfl⟩; simpa using hy
    rw [hpre]
    exact Measure.count_injective_image (f := fun y : ℤ => y - t)
      (fun a b h => by simpa using h) s
  have hmp : MeasurePreserving (fun x : ℤ => x + t) Measure.count Measure.count :=
    ⟨Measurable.of_discrete, hmap⟩
  exact eLpNorm_comp_measurePreserving (p := p) (g := X)
    (Measurable.of_discrete.aestronglyMeasurable (μ := Measure.count)) hmp

end Work.KMTAreas.A4Z
