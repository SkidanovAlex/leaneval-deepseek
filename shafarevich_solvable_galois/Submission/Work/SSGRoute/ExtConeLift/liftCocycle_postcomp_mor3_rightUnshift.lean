import Mathlib.Combinatorics.Quiver.ReflQuiver
import Mathlib.Algebra.Homology.HomotopyCategory.Pretriangulated
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.ExtConeLift

open CategoryTheory Limits CochainComplex HomComplex

universe u v

section aux

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasBinaryBiproducts C]
  {F G : CochainComplex C ℤ} (φ : F ⟶ G) [HomologicalComplex.HasHomotopyCofiber φ]

set_option backward.isDefEq.respectTransparency false in
/-- The degree `0` cochain of `mor₃` of the mapping cone triangle, right-unshifted, is the
cocycle `-fst φ` (which is the `1`-cocycle giving `mor₃`). -/
lemma mappingCone_ofHom_triangle_mor₃_rightUnshift :
    (Cochain.ofHom (mappingCone.triangle φ).mor₃).rightUnshift 1 (zero_add 1)
      = -(↑(mappingCone.fst φ) : Cochain (mappingCone φ) F 1) := by
  have h1 : Cochain.ofHom (mappingCone.triangle φ).mor₃
      = (-(↑(mappingCone.fst φ) : Cochain (mappingCone φ) F 1)).rightShift 1 0 (zero_add 1) := by
    rw [show (mappingCone.triangle φ).mor₃
        = Cocycle.homOf ((-(mappingCone.fst φ)).rightShift 1 0 (zero_add 1)) from rfl]
    exact Cocycle.cochain_ofHom_homOf_eq_coe _
  rw [h1]
  exact Cochain.rightUnshift_rightShift _ 1 0 (zero_add 1)

set_option backward.isDefEq.respectTransparency false in
/-- The `α`-part of `liftCochain φ α β`, postcomposed with `mor₃` and right-unshifted,
is `-α`. -/
lemma mappingCone_liftCochain_alpha_rightUnshift {K : CochainComplex C ℤ} {n : ℤ}
    (α : Cocycle K F (n + 1)) (h1 : (n + 1) + (-1) = n) :
    (((α : Cochain K F (n + 1)).comp (mappingCone.inl φ) h1).comp
        (Cochain.ofHom (mappingCone.triangle φ).mor₃) (add_zero n)).rightUnshift (n + 1) (by omega)
      = -(α : Cochain K F (n + 1)) := by
  rw [Cochain.rightUnshift_comp (γ := (α : Cochain K F (n + 1)).comp (mappingCone.inl φ) h1)
    (γ' := Cochain.ofHom (mappingCone.triangle φ).mor₃) (hnm := add_zero n) (nm' := n + 1)
    (hnm' := by omega) (m' := 1) (hm' := zero_add 1)]
  rw [mappingCone_ofHom_triangle_mor₃_rightUnshift φ, Cochain.comp_neg]
  rw [Cochain.comp_assoc (h₂₃ := neg_add_cancel 1) (h₁₂₃ := by omega)]
  rw [mappingCone.inl_fst, Cochain.comp_id]

set_option backward.isDefEq.respectTransparency false in
/-- The `β`-part of `liftCochain φ α β`, postcomposed with `mor₃` and right-unshifted,
is zero. -/
lemma mappingCone_liftCochain_beta_rightUnshift {K : CochainComplex C ℤ} {n : ℤ}
    (β : Cochain K G n) (h3 : n + 0 = n) :
    ((β.comp (Cochain.ofHom (mappingCone.inr φ)) h3).comp
        (Cochain.ofHom (mappingCone.triangle φ).mor₃) (add_zero n)).rightUnshift (n + 1) (by omega)
      = 0 := by
  rw [Cochain.rightUnshift_comp (γ := β.comp (Cochain.ofHom (mappingCone.inr φ)) h3)
    (γ' := Cochain.ofHom (mappingCone.triangle φ).mor₃) (hnm := add_zero n) (nm' := n + 1)
    (hnm' := by omega) (m' := 1) (hm' := zero_add 1)]
  rw [mappingCone_ofHom_triangle_mor₃_rightUnshift φ, Cochain.comp_neg]
  rw [Cochain.comp_assoc (h₂₃ := zero_add 1) (h₁₂₃ := by omega)]
  rw [mappingCone.inr_fst, Cochain.comp_zero]
  simp

end aux

section main

set_option backward.isDefEq.respectTransparency false

/-- For a morphism `S.f : S.X₁ ⟶ S.X₂` of cochain complexes, a cochain `β : K ⟶ S.X₂` of degree `n`
and a cocycle `α : K ⟶ S.X₁` of degree `n+1` satisfying the mapping-cone relation
`δ β + α.comp (ofHom S.f) = 0`, the cocycle `liftCocycle S.f α β` (a lift of `β.comp (ofHom S.g)`
through the mapping cone of `S.f`) has, after postcomposition with `mor₃` of the mapping cone triangle
and unshifting, the class `-α`. -/
theorem liftCocycle_postcomp_mor3_rightUnshift {C : Type u} [Category.{v} C] [Abelian C]
    {S : ShortComplex (CochainComplex C ℤ)} {K : CochainComplex C ℤ} {n : ℤ}
    (β : Cochain K S.X₂ n) (α : Cocycle K S.X₁ (n + 1))
    (eq : δ n (n + 1) β + (α : Cochain K S.X₁ (n + 1)).comp
        (Cochain.ofHom S.f) (add_zero (n + 1)) = 0) :
    ((CochainComplex.mappingCone.liftCocycle S.f α β rfl eq).postcomp
        (CochainComplex.mappingCone.triangle S.f).mor₃).rightUnshift (n + 1) (by omega) =
      -α := by
  apply Cocycle.ext
  rw [Cocycle.rightUnshift_coe, Cocycle.postcomp_coe,
    CochainComplex.mappingCone.liftCocycle_coe, Cocycle.coe_neg]
  simp only [CochainComplex.mappingCone.liftCochain]
  rw [Cochain.add_comp, Cochain.rightUnshift_add,
    mappingCone_liftCochain_alpha_rightUnshift, mappingCone_liftCochain_beta_rightUnshift]
  simp

end main

end Work.SSGRoute.ExtConeLift
