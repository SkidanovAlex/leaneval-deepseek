/-
# The affine chart of a base change and the map `Γ(C,W) ⊗[k] F ⟶ K(C')`

For a curve `C` over a field `k`, a field extension `F/k`, a base-change square
`S : BCSquare C C'` and an affine open `W ⊆ C`, this file sets up the affine description of
the preimage `S.π ⁻¹ᵁ W`: it is affine, its coordinate ring is `Γ(C,W) ⊗[k] F` and the
resulting map `Γ(C,W) ⊗[k] F ⟶ K(C')` is injective.

This is the affine input to the injectivity of `tensorLift`.
-/
import Mathlib
import Submission.Work.CurveBasics.Curve.BCSquare.fieldMapTensor
import Submission.Work.CurveBasics.Curve.BCSquare.GermNaturality
import Submission.Work.CurveBasics.BaseChange.isPullback_spec_affine
import Submission.Work.CurveBasics.BaseChange.krullDim_le_one

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open Work.CurveBasics CategoryTheory Limits AlgebraicGeometry
open scoped TensorProduct

set_option autoImplicit false
set_option linter.style.haveILetI false

universe u

namespace Work.CurveBasics.Curve.BCSquare

variable {k : Type u} [Field k] {F : Type u} [Field F] [Algebra k F]
variable {C : Curve k} {C' : Curve F}

noncomputable section

/-! ## The affine square of a base change -/

/-- The projection of a base-change square is an affine morphism: it is the base change of the
affine morphism `Spec F ⟶ Spec k`. -/
instance isAffineHom_π (S : BCSquare C C') : IsAffineHom S.π :=
  MorphismProperty.IsStableUnderBaseChange.of_isPullback S.isPullback.flip
    (BaseChange.isAffineHom_specMap (k := k) F)

/-- The preimage in `C'` of an affine open of `C` is affine. -/
theorem isAffineOpen_preimage (S : BCSquare C C') (W : C.left.Opens)
    (hW : AlgebraicGeometry.IsAffineOpen W) : AlgebraicGeometry.IsAffineOpen (S.π ⁻¹ᵁ W) :=
  hW.preimage S.π

/-- The pasted square describing the preimage of an open set under the projection of a
base-change square. -/
theorem paste_square (S : BCSquare C C') (W : C.left.Opens) :
    IsPullback (S.π ∣_ W) ((S.π ⁻¹ᵁ W).ι ≫ C'.hom) (W.ι ≫ C.hom) (specMap k F) :=
  (isPullback_morphismRestrict S.π W).paste_vert S.isPullback

/-- For the projection of a base-change square and an affine open `W ⊆ C`, the morphism
`Spec Γ(C',π⁻¹W) ⟶ Spec Γ(C,W)` induced by `S.π.app W` is, under the canonical isomorphisms
`Spec Γ(X,U) ≅ U`, the restriction `S.π ∣_ W`. -/
theorem isoSpec_hom_specMap_π (S : BCSquare C C') (W : C.left.Opens)
    (hW : IsAffineOpen W) :
    (isAffineOpen_preimage S W hW).isoSpec.hom ≫ Spec.map (S.π.app W)
      = (S.π ∣_ W) ≫ hW.isoSpec.hom := by
  have hV : IsAffineOpen (S.π ⁻¹ᵁ W) := isAffineOpen_preimage S W hW
  show hV.isoSpec.hom ≫ Spec.map (S.π.app W) = (S.π ∣_ W) ≫ hW.isoSpec.hom
  have h := IsAffineOpen.SpecMap_appLE_fromSpec (f := S.π)
    (V := S.π ⁻¹ᵁ W) (U := W) hW hV le_rfl
  rw [Scheme.Hom.appLE_eq_app (f := S.π) (U := W)] at h
  simp only [IsAffineOpen.fromSpec] at h
  rw [Category.assoc] at h
  rw [← morphismRestrict_ι S.π W] at h
  have h2 : Spec.map (S.π.app W) ≫ hW.isoSpec.inv
      = hV.isoSpec.inv ≫ (S.π ∣_ W) := by
    refine (cancel_mono W.ι).mp ?_
    simpa only [Category.assoc] using h
  have h4 : Spec.map (S.π.app W)
      = (hV.isoSpec.inv ≫ (S.π ∣_ W)) ≫ hW.isoSpec.hom :=
    (Iso.comp_inv_eq _).mp h2
  rw [h4]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]

/-- **The affine description of a base-change square.**  For an affine open `W ⊆ C` the square

```
Spec Γ(C', π⁻¹W) --Spec (S.π.app W)--> Spec Γ(C, W)
        |                                      |
        v                                      v
      Spec F ---------Spec (algebraMap k F)--> Spec k
```

is a pullback. -/
theorem isPullback_spec_preimage (S : BCSquare C C') (W : C.left.Opens)
    (hW : IsAffineOpen W) :
    IsPullback (Spec.map (S.π.app W))
      (Spec.map (CommRingCat.ofHom (algebraMap F Γ(C'.left, S.π ⁻¹ᵁ W))))
      (Spec.map (CommRingCat.ofHom (algebraMap k Γ(C.left, W))))
      (specMap k F) := by
  have hV : IsAffineOpen (S.π ⁻¹ᵁ W) := isAffineOpen_preimage S W hW
  -- replace the structure morphism `W.ι ≫ C.hom` by `Spec` of the algebra structure map
  have h₁ : IsPullback ((S.π ∣_ W) ≫ hW.isoSpec.hom)
      ((S.π ⁻¹ᵁ W).ι ≫ C'.hom)
      (Spec.map (CommRingCat.ofHom (algebraMap k Γ(C.left, W)))) (specMap k F) :=
    (paste_square S W).of_iso (Iso.refl _) hW.isoSpec (Iso.refl _) (Iso.refl _)
      (by simp) (by simp) (BaseChange.iota_comp_hom C W hW) (by simp)
  refine h₁.of_iso' hV.isoSpec.symm (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_ (by simp) (by simp)
  · exact (Iso.inv_comp_eq _).mpr (isoSpec_hom_specMap_π S W hW).symm
  · rw [BaseChange.iota_comp_hom C' (S.π ⁻¹ᵁ W) hV]
    simp

/-! ## The algebra structures on the sections of a curve -/

/-- The `k`-algebra structure on the sections of a curve over `k` is compatible with the
`k`-algebra structure on the function field. -/
theorem sections_algebraMap_eq (C : Curve k) (W : C.left.Opens) [Nonempty W] (c : k) :
    algebraMap Γ(C.left, W) C.functionField (algebraMap k Γ(C.left, W) c)
      = algebraMap k C.functionField c := by
  have hCt : Nonempty (⊤ : C.left.Opens) := ⟨⟨genericPoint C.left, trivial⟩⟩
  haveI := hCt
  have h1 : algebraMap k Γ(C.left, W) c
      = (C.hom.appLE ⊤ W (by simp)) ((Scheme.ΓSpecIso (CommRingCat.of k)).inv c) := by
    simp only [RingHom.algebraMap_toAlgebra, ConcreteCategory.comp_apply]
  have h2 : algebraMap k C.functionField c
      = C.left.germToFunctionField ⊤
          (C.hom.appTop ((Scheme.ΓSpecIso (CommRingCat.of k)).inv c)) := by
    simp only [RingHom.algebraMap_toAlgebra, ConcreteCategory.comp_apply]
  rw [h1, h2, RingHom.algebraMap_toAlgebra]
  simp only [Scheme.Hom.appLE, ConcreteCategory.comp_apply]
  rw [TopCat.Presheaf.germ_res_apply]
  rfl

/-- The `k`-algebra structure on the sections of a curve is a scalar tower with the function
field. -/
theorem isScalarTower_sections (C : Curve k) (W : C.left.Opens) [Nonempty W] :
    IsScalarTower k Γ(C.left, W) C.functionField :=
  IsScalarTower.of_algebraMap_eq
    (fun c => (sections_algebraMap_eq C W c).symm)

/-- The germ map to the function field is a map of `k`-algebras. -/
theorem germToFunctionField_algebraMap (C : Curve k) (W : C.left.Opens) [Nonempty W] (c : k) :
    (C.germToFunctionField W).hom (algebraMap k Γ(C.left, W) c) = algebraMap k C.functionField c :=
  sections_algebraMap_eq C W c

/-! ## The naturality of `fieldMap` on a section -/

/-- The map on function fields induced by a base-change square is compatible with the
canonical maps from the sections. -/
theorem fieldMap_germToFunctionField (S : BCSquare C C') (W : C.left.Opens) [Nonempty W]
    [Nonempty (S.π ⁻¹ᵁ W)] (a : Γ(C.left, W)) :
    S.fieldMap.hom ((C.germToFunctionField W).hom a)
      = (C'.germToFunctionField (S.π ⁻¹ᵁ W)).hom ((S.π.app W).hom a) := by
  have h : C.germToFunctionField W ≫ S.fieldMap
      = S.π.app W ≫ C'.germToFunctionField (S.π ⁻¹ᵁ W) := by
    rw [Curve.BCSquare.fieldMap, ← Category.assoc, TopCat.Presheaf.germ_stalkSpecializes,
      Scheme.Hom.germ_stalkMap]
  simpa only [ConcreteCategory.comp_apply] using ConcreteCategory.congr_hom h a

/-! ## The ring isomorphism `Γ(C,W) ⊗[k] F ≅ Γ(C', π⁻¹W)` -/

/-- The canonical identification of the sections over the preimage of an affine open with the
tensor product `Γ(C,W) ⊗[k] F`, obtained by comparing the affine square of
`isPullback_spec_preimage` with the pullback of affine schemes `Spec (Γ(C,W) ⊗[k] F)`. -/
noncomputable def sectionsLift (S : BCSquare C C') (W : C.left.Opens) (hW : IsAffineOpen W) :
    (Γ(C.left, W) ⊗[k] F) →+* Γ(C'.left, S.π ⁻¹ᵁ W) :=
  (Spec.preimage ((isPullback_spec_preimage S W hW).isoPullback ≪≫
    pullbackSpecIso k Γ(C.left, W) F).hom).hom

/-- `sectionsLift` is injective, being the ring hom underlying an isomorphism of schemes. -/
theorem sectionsLift_injective (S : BCSquare C C') (W : C.left.Opens)
    (hW : IsAffineOpen W) : Function.Injective (sectionsLift S W hW) := by
  set u := (isPullback_spec_preimage S W hW).isoPullback ≪≫ pullbackSpecIso k Γ(C.left, W) F
    with hu
  have hleft : Function.LeftInverse (fun z => (Spec.preimage u.inv).hom z)
      (fun z => (Spec.preimage u.hom).hom z) := by
    intro z
    have hid : (Spec.preimage u.hom ≫ Spec.preimage u.inv :
        CommRingCat.of (Γ(C.left, W) ⊗[k] F) ⟶ CommRingCat.of (Γ(C.left, W) ⊗[k] F)) =
        𝟙 _ := by
      apply Spec.map_injective
      rw [Spec.map_comp, Spec.map_preimage, Spec.map_preimage, Spec.map_id]
      exact Iso.inv_hom_id u
    exact congrArg (fun (φ : CommRingCat.of (Γ(C.left, W) ⊗[k] F) ⟶
      CommRingCat.of (Γ(C.left, W) ⊗[k] F)) => φ.hom z) hid
  exact hleft.injective

/-- `sectionsLift` sends `a ⊗ 1` to the image of the section `a` under the projection. -/
theorem sectionsLift_tmul_one (S : BCSquare C C') (W : C.left.Opens) (hW : IsAffineOpen W)
    (a : Γ(C.left, W)) :
    sectionsLift S W hW (a ⊗ₜ[k] (1 : F)) = (S.π.app W).hom a := by
  set u := (isPullback_spec_preimage S W hW).isoPullback ≪≫ pullbackSpecIso k Γ(C.left, W) F
    with hu
  have hcomp : u.hom ≫ Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom
      (R := k) (A := Γ(C.left, W)) (B := F))) = Spec.map (S.π.app W) := by
    rw [hu, Iso.trans_hom, Category.assoc, pullbackSpecIso_hom_fst,
      IsPullback.isoPullback_hom_fst]
  have hring : CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom
      (R := k) (A := Γ(C.left, W)) (B := F)) ≫ Spec.preimage u.hom
      = S.π.app W := by
    apply Spec.map_injective
    rw [Spec.map_comp, Spec.map_preimage]
    exact hcomp
  have hpoint := ConcreteCategory.congr_hom hring a
  rw [ConcreteCategory.comp_apply, CommRingCat.ofHom_apply,
    Algebra.TensorProduct.includeLeftRingHom_apply] at hpoint
  rw [hu] at hpoint
  exact hpoint

/-- `sectionsLift` sends `1 ⊗ c` to the constant `c`. -/
theorem sectionsLift_one_tmul (S : BCSquare C C') (W : C.left.Opens) (hW : IsAffineOpen W)
    (c : F) :
    sectionsLift S W hW ((1 : Γ(C.left, W)) ⊗ₜ[k] c)
      = algebraMap F Γ(C'.left, S.π ⁻¹ᵁ W) c := by
  set u := (isPullback_spec_preimage S W hW).isoPullback ≪≫ pullbackSpecIso k Γ(C.left, W) F
    with hu
  have hcomp : u.hom ≫ Spec.map (CommRingCat.ofHom (↑(Algebra.TensorProduct.includeRight
      (R := k) (A := Γ(C.left, W)) (B := F)) : F →+* (Γ(C.left, W) ⊗[k] F)))
      = Spec.map (CommRingCat.ofHom (algebraMap F Γ(C'.left, S.π ⁻¹ᵁ W))) := by
    rw [hu, Iso.trans_hom, Category.assoc]
    simp only [pullbackSpecIso_hom_snd]
    exact IsPullback.isoPullback_hom_snd (isPullback_spec_preimage S W hW)
  have hring : CommRingCat.ofHom (↑(Algebra.TensorProduct.includeRight
      (R := k) (A := Γ(C.left, W)) (B := F)) : F →+* (Γ(C.left, W) ⊗[k] F))
      ≫ Spec.preimage u.hom
      = CommRingCat.ofHom (algebraMap F Γ(C'.left, S.π ⁻¹ᵁ W)) := by
    apply Spec.map_injective
    rw [Spec.map_comp, Spec.map_preimage]
    exact hcomp
  have hpoint := ConcreteCategory.congr_hom hring c
  rw [ConcreteCategory.comp_apply, CommRingCat.ofHom_apply] at hpoint
  have hiri : (↑(Algebra.TensorProduct.includeRight (R := k) (A := Γ(C.left, W)) (B := F)) :
      F →+* (Γ(C.left, W) ⊗[k] F)) c = 1 ⊗ₜ[k] c := by
    simpa using Algebra.TensorProduct.includeRight_apply (R := k) (A := Γ(C.left, W)) (B := F) c
  rw [hiri, CommRingCat.ofHom_apply, hu] at hpoint
  exact hpoint

/-! ## Extensionality for ring homomorphisms out of a tensor product -/

/-- Two ring homomorphisms out of a tensor product which agree on `a ⊗ 1` and on `1 ⊗ b`
agree everywhere. -/
theorem ringHom_ext_tensor {R A B C : Type*} [CommSemiring R] [Semiring A] [Semiring B]
    [Semiring C] [Algebra R A] [Algebra R B] {f g : A ⊗[R] B →+* C}
    (h1 : ∀ a, f (a ⊗ₜ[R] (1 : B)) = g (a ⊗ₜ[R] (1 : B)))
    (h2 : ∀ b, f ((1 : A) ⊗ₜ[R] b) = g ((1 : A) ⊗ₜ[R] b)) : f = g := by
  refine RingHom.ext fun z => ?_
  have h3 : ∀ a b, f (a ⊗ₜ[R] b) = g (a ⊗ₜ[R] b) := by
    intro a b
    have e : (a ⊗ₜ[R] (1 : B)) * ((1 : A) ⊗ₜ[R] b) = a ⊗ₜ[R] b := by
      rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    rw [← e, map_mul, map_mul, h1 a, h2 b]
  refine TensorProduct.inductionOn (motive := fun w => f w = g w) z ?_ ?_
  · intro a b
    exact h3 a b
  · intro x y hx hy
    rw [map_add, map_add, hx, hy]

end

end Work.CurveBasics.Curve.BCSquare
