import Mathlib
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.LocalFields

/-- If `A → B` is a surjective local homomorphism of local rings, then the induced map of
residue fields `κ(A) → κ(B)` is an algebra isomorphism, so `κ(B)` is one-dimensional over
`κ(A)`. -/
theorem finrank_residueField_eq_one_of_surjective {A B : Type*} [CommRing A] [IsLocalRing A]
    [CommRing B] [IsLocalRing B] [Algebra A B] [IsLocalHom (algebraMap A B)]
    (h : Function.Surjective (algebraMap A B)) :
    Module.finrank (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField B) = 1 := by
  -- The induced map on residue fields is surjective.
  have hsurj : Function.Surjective
      (algebraMap (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField B)) := by
    intro y
    obtain ⟨b, rfl⟩ := IsLocalRing.residue_surjective y
    obtain ⟨a, rfl⟩ := h b
    exact ⟨IsLocalRing.residue A a, IsLocalRing.ResidueField.algebraMap_residue a⟩
  -- Hence every element of `κ(B)` is a scalar multiple of `1`.
  refine finrank_eq_one (1 : IsLocalRing.ResidueField B) one_ne_zero ?_
  intro w
  obtain ⟨c, rfl⟩ := hsurj w
  exact ⟨c, (Algebra.algebraMap_eq_smul_one c).symm⟩

end Work.LocalFields
