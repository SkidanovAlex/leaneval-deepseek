import Mathlib

namespace Work.WilE2.WilE2Aux

theorem isPreconnected_preimage_subtype_val {α : Type*} [TopologicalSpace α] {X C : Set α}
    (hCX : C ⊆ X) (hC : IsPreconnected C) :
    IsPreconnected (Subtype.val ⁻¹' C : Set ↥X) := by
  -- `Subtype.val : ↥X → α` is an inducing map, so preconnectedness is reflected
  -- along it: it suffices to show `Subtype.val '' (Subtype.val ⁻¹' C)` is preconnected.
  have h := (Topology.IsInducing.subtypeVal (t := X)).isPreconnected_image
    (s := (Subtype.val ⁻¹' C : Set ↥X))
  -- the image is exactly `X ∩ C`, which is `C` because `C ⊆ X`.
  rw [Subtype.image_preimage_val, Set.inter_eq_right.mpr hCX] at h
  exact h.mp hC

end Work.WilE2.WilE2Aux
