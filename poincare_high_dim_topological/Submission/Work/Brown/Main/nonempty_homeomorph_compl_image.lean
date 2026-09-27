import Mathlib
import Submission.Work.Brown.Basic

namespace Work.Brown.Main

/-- If `f : X → Y` is a continuous surjection from a compact space to a Hausdorff space,
`f` is injective on `Aᶜ` and `f` separates points of `Aᶜ` from points of `A`, then the
restriction of `f` induces a homeomorphism `Aᶜ ≃ₜ (f '' A)ᶜ`. -/
theorem nonempty_homeomorph_compl_image {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [CompactSpace X] [T2Space Y] (f : X → Y) (hf : Continuous f) (hfs : Function.Surjective f)
    (A : Set X) (hA : IsClosed A) (hinj : Set.InjOn f Aᶜ)
    (hsep : ∀ x ∉ A, ∀ a ∈ A, f x ≠ f a) : Nonempty (↥(Aᶜ) ≃ₜ ↥((f '' A)ᶜ)) := by
  -- The map induced by `f` on the complement of `A`.
  let φ : ↥(Aᶜ) → ↥((f '' A)ᶜ) := fun x => ⟨f x.val, by
    rw [Set.mem_compl_iff, Set.mem_image]
    rintro ⟨a, ha, hfa⟩
    exact hsep x.val x.2 a ha hfa.symm⟩
  -- `φ` is continuous.
  have hcont : Continuous φ := by
    apply Continuous.subtype_mk
    exact hf.comp continuous_subtype_val
  -- `φ` is injective: it is the restriction of the injective-on-`Aᶜ` map `f`.
  have hinj' : Function.Injective φ := by
    intro x y hxy
    have h1 : f x.val = f y.val := by
      have := congrArg Subtype.val hxy; simpa using this
    exact Subtype.ext (hinj x.2 y.2 h1)
  -- `φ` is surjective: every point off `f '' A` has its (surjective) preimage off `A`.
  have hsurj' : Function.Surjective φ := by
    intro y
    obtain ⟨x, hx⟩ := hfs y.val
    have hxA : x ∉ A := by
      intro hxmem
      exact y.2 (hx ▸ ⟨x, hxmem, rfl⟩)
    refine ⟨⟨x, hxA⟩, ?_⟩
    apply Subtype.ext
    simpa using hx
  -- `φ` is a closed map, being the restriction of the closed map `f`
  -- (continuous from compact to Hausdorff) to the complement of a set.
  have hclosed : IsClosedMap φ := by
    intro C hC
    rw [isClosed_induced_iff] at hC
    obtain ⟨D, hD, hDC⟩ := hC
    rw [isClosed_induced_iff]
    refine ⟨f '' D, hf.isClosedMap D hD, ?_⟩
    have hmemC : ∀ x : ↥(Aᶜ), (x ∈ C) ↔ (x.val ∈ D) := by
      intro x
      rw [← hDC, Set.mem_preimage]
    ext y
    rw [Set.mem_preimage]
    constructor
    · intro hy
      obtain ⟨z, hzD, hzf⟩ := hy
      have hzA : z ∉ A := by
        intro hzmem
        exact y.2 (hzf ▸ ⟨z, hzmem, rfl⟩)
      refine ⟨⟨z, hzA⟩, ?_, ?_⟩
      · exact (hmemC ⟨z, hzA⟩).mpr hzD
      · exact Subtype.ext hzf
    · rintro ⟨x, hxC, hxφ⟩
      refine ⟨x.val, (hmemC x).mp hxC, ?_⟩
      have := congrArg Subtype.val hxφ
      simpa using this
  -- A continuous bijective closed map is a homeomorphism.
  let e : ↥(Aᶜ) ≃ ↥((f '' A)ᶜ) := Equiv.ofBijective φ ⟨hinj', hsurj'⟩
  exact ⟨e.toHomeomorphOfContinuousClosed (by change Continuous φ; exact hcont)
    (by change IsClosedMap φ; exact hclosed)⟩

end Work.Brown.Main
