import Mathlib

/-!
# Image-preimage identity for subcomplexes of a simplicial set

For a subcomplex `Λ` of a simplicial set `Y` and a morphism `f : X ⟶ Y`, the image under `f`
of the preimage of `Λ` is exactly the intersection of `Λ` with the range of `f`:
`(Λ.preimage f).image f = Λ ⊓ SSet.Subcomplex.range f`.

Both sides are computed simplex-wise by the elementary set identity
`f '' (f ⁻¹' Λ) = Λ ∩ range f`.
-/

namespace Work.SSS

open CategoryTheory

theorem image_preimage_eq_inf_range {X Y : SSet.{0}} (Λ : Y.Subcomplex) (f : X ⟶ Y) :
    (Λ.preimage f).image f = Λ ⊓ SSet.Subcomplex.range f := by
  apply le_antisymm
  · -- `(Λ.preimage f).image f` is contained both in `Λ` and in the range of `f`
    exact le_inf (SSet.Subcomplex.image_preimage_le Λ f) (SSet.Subcomplex.image_le_range _ f)
  · -- conversely, a simplex of `Λ` lying in the range of `f` is hit by a simplex of the preimage
    intro n y hy
    obtain ⟨hyΛ, hyr⟩ := hy
    obtain ⟨x, rfl⟩ := hyr
    exact ⟨x, hyΛ, rfl⟩

end Work.SSS
