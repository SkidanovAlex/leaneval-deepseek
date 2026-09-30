import Mathlib
set_option backward.isDefEq.respectTransparency false  -- v435port
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

variable {R : Type} [CommRing R] [Nontrivial R]

namespace Work.SSSR

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

end Work.SSSR
