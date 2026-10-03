import Mathlib

namespace Work.Horn

/-- A continuous open map that is injective on an open set `A` maps `↥A` homeomorphically onto
`↥(f '' A)`. -/
theorem homeomorph_image_of_injOn {f : ℂ → ℂ} (hcont : Continuous f) (hop : IsOpenMap f)
    {A : Set ℂ} (hA : IsOpen A) (hinj : Set.InjOn f A) :
    ∃ H : ↥A ≃ₜ ↥(f '' A), ∀ a : ↥A, (H a : ℂ) = f (a : ℂ) := by
  let g : ↥A → ℂ := fun a => f (a : ℂ)
  have hgcont : Continuous g := hcont.comp continuous_subtype_val
  have hginj : Function.Injective g := by
    intro a b hab
    exact Subtype.ext (hinj a.2 b.2 hab)
  have hgopen : IsOpenMap g := hop.comp hA.isOpenEmbedding_subtypeVal.isOpenMap
  have hgemb : Topology.IsEmbedding g :=
    (Topology.IsOpenEmbedding.of_continuous_injective_isOpenMap hgcont hginj hgopen).isEmbedding
  have hrange : Set.range g = f '' A := by
    ext y; constructor
    · rintro ⟨a, rfl⟩; exact ⟨a, a.2, rfl⟩
    · rintro ⟨x, hx, rfl⟩; exact ⟨⟨x, hx⟩, rfl⟩
  refine ⟨hgemb.toHomeomorph.trans (Homeomorph.setCongr hrange), ?_⟩
  intro a
  simp only [Homeomorph.trans_apply]
  change ((hgemb.toHomeomorph a : Set.range g) : ℂ) = f ↑a
  rw [Topology.IsEmbedding.toHomeomorph_apply_coe]

end Work.Horn
