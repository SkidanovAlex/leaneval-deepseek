import Mathlib

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.CY3Stab.Prod

open CategoryTheory CategoryTheory.Limits in
/-- Pushing out along a composite with an isomorphism is the same as pushing out along the
second map: if `φ : A ⟶ A'` is an isomorphism, then the pushout of the span
`A --φ ≫ f--> B`, `A --φ ≫ g--> C` is canonically isomorphic to the pushout of the span
`f : A' ⟶ B`, `g : A' ⟶ C`. -/
theorem pushout_iso_of_iso_base {A A' B C : CommRingCat} (φ : A ⟶ A') [IsIso φ] (f : A' ⟶ B) (g : A' ⟶ C) : Nonempty (pushout (φ ≫ f) (φ ≫ g) ≅ pushout f g) := by
  refine ⟨Iso.mk
    (pushout.desc (f := φ ≫ f) (g := φ ≫ g) (pushout.inl f g) (pushout.inr f g) (by
      simp only [Category.assoc, pushout.condition]))
    (pushout.desc (f := f) (g := g) (pushout.inl (φ ≫ f) (φ ≫ g)) (pushout.inr (φ ≫ f) (φ ≫ g)) (by
      refine (cancel_epi φ).mp ?_
      rw [← Category.assoc, ← Category.assoc, pushout.condition]))
    ?_ ?_⟩
  · refine pushout.hom_ext (f := φ ≫ f) (g := φ ≫ g) ?_ ?_
    · simp only [← Category.assoc, pushout.inl_desc, Category.comp_id]
    · simp only [← Category.assoc, pushout.inr_desc, Category.comp_id]
  · refine pushout.hom_ext (f := f) (g := g) ?_ ?_
    · simp only [← Category.assoc, pushout.inl_desc, Category.comp_id]
    · simp only [← Category.assoc, pushout.inr_desc, Category.comp_id]

end Work.CY3Stab.Prod
