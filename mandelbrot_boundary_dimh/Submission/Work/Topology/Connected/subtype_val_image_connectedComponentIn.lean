import Mathlib

namespace Work.Topology.Connected

/-- Connected components of subsets of a subspace correspond to connected components of the
corresponding subsets of the ambient space.

Suggested proof: `Subtype.val : ↥K → α` is an embedding with image `K`; if `x ∉ F` both sides are
`∅` (definitially, since `connectedComponentIn F x = ∅` and `↑x ∉ Subtype.val '' F`), and if
`x ∈ F` then `Subtype.val` restricts to a homeomorphism `↥F ≃ₜ ↥(Subtype.val '' F)` and
`Homeomorph.image_connectedComponentIn` (`Mathlib.Topology.Homeomorph.Lemmas`) applies. -/
theorem subtype_val_image_connectedComponentIn {α : Type*} [TopologicalSpace α] {K : Set α}
    {F : Set ↥K} {x : ↥K} :
    Subtype.val '' (connectedComponentIn F x) = connectedComponentIn (Subtype.val '' F) ↑x := by
  by_cases hx : x ∈ F
  · -- `x ∈ F`: `Subtype.val` is continuous, giving one inclusion for free.
    apply subset_antisymm
    · exact (continuous_subtype_val.continuousOn (s := F)).image_connectedComponentIn_subset hx
    · -- For the reverse inclusion, the preimage of the ambient component, cut down to `F`,
      -- is preconnected (its image under the inducing map `Subtype.val` is exactly the
      -- ambient component) and contains `x`, so it lies in the component of `x` in `F`.
      intro y hy
      have hAx : (↑x : α) ∈ connectedComponentIn (Subtype.val '' F) ↑x :=
        mem_connectedComponentIn (Set.mem_image_of_mem Subtype.val hx)
      have hsub : connectedComponentIn (Subtype.val '' F) ↑x ⊆ Subtype.val '' F :=
        connectedComponentIn_subset _ _
      have hSpre : Subtype.val '' (Subtype.val ⁻¹' (connectedComponentIn (Subtype.val '' F) ↑x) ∩ F)
          = connectedComponentIn (Subtype.val '' F) ↑x := by
        apply subset_antisymm
        · rintro _ ⟨z, ⟨hz, _⟩, rfl⟩; exact hz
        · intro a ha
          obtain ⟨z, hzF, hza⟩ := hsub ha
          exact ⟨z, ⟨by rw [Set.mem_preimage, hza]; exact ha, hzF⟩, hza⟩
      have hpre : IsPreconnected (Subtype.val ⁻¹' (connectedComponentIn (Subtype.val '' F) ↑x) ∩ F) :=
        (Topology.IsInducing.subtypeVal.isPreconnected_image).mp
          (by rw [hSpre]; exact isPreconnected_connectedComponentIn)
      have hsub2 : Subtype.val ⁻¹' (connectedComponentIn (Subtype.val '' F) ↑x) ∩ F ⊆
          connectedComponentIn F x :=
        hpre.subset_connectedComponentIn ⟨hAx, hx⟩ Set.inter_subset_right
      obtain ⟨z, hzF, hza⟩ := hsub hy
      exact ⟨z, hsub2 ⟨by rw [Set.mem_preimage, hza]; exact hy, hzF⟩, hza⟩
  · -- `x ∉ F`: both sides are empty.
    rw [connectedComponentIn_eq_empty hx, Set.image_empty,
        connectedComponentIn_eq_empty (show (↑x : α) ∉ Subtype.val '' F from ?_)]
    rintro ⟨z, hzF, hzx⟩
    exact hx ((Subtype.ext hzx) ▸ hzF)

end Work.Topology.Connected
