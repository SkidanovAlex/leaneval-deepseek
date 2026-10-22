import Mathlib
import Submission.Work.RESOL.SigmaSetup

namespace Work.ANALYTIC

open CategoryTheory CategoryTheory.Limits LightCondensed

noncomputable section

/-!
# `singleFunctor LightCondAb 0` preserves small coproducts

The functor `CochainComplex.singleFunctor C 0` (a complex concentrated in degree `0`) has a right
adjoint, namely the functor sending a cochain complex `K` to the kernel of `K.d 0 1`; in
particular it preserves coproducts.  We do not formalise the adjunction: instead we produce the
two ingredients explicitly.

* `singleHomEquiv A K` is the (contravariant) bijection, natural in `A`, between morphisms
  `(single C 0).obj A ⟶ K` and morphisms `A ⟶ K.X 0` killed by `K.d 0 1`.  Concretely it is the
  "restriction to the degree `0` component", conjugated by the canonical isomorphism
  `((single C 0).obj A).X 0 ≅ A`.  `singleHomEquiv_map` records that it is natural, i.e. that
  precomposition with `(single C 0).map u` corresponds to `u ≫ ·`.
* `sigmaHomEquiv X d` is the universal property of the coproduct `∐ X`, for morphisms into the
  object `W` killed by a fixed morphism `d : W ⟶ W'`: the map sending `f : ∐ X ⟶ W` to the family
  `j ↦ Sigma.ι X j ≫ f` is a bijection onto the corresponding families.

Composing the two gives the statement: a morphism `(single C 0).obj (∐ A) ⟶ Z` is the same as a
family of morphisms `(single C 0).obj (A j) ⟶ Z`.
-/

/-- The morphisms out of a cochain complex concentrated in degree `0` are the morphisms out of
its degree `0` term which are killed by the differential `d 0 1`.  The bijection is contravariant
in `A`; see `singleHomEquiv_map` for its naturality. -/
def singleHomEquiv {C : Type*} [Category C] [Preadditive C] [HasZeroObject C]
    (A : C) (K : CochainComplex C ℤ) :
    (((CochainComplex.singleFunctor C 0).obj A) ⟶ K) ≃
      { f : A ⟶ K.X 0 // f ≫ K.d 0 1 = 0 } where
  toFun φ := ⟨(HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 A).inv ≫ φ.f 0, by
    rw [Category.assoc]
    have h := φ.comm 0 1
    rw [CochainComplex.singleFunctor_obj_d, zero_comp] at h
    rw [h, comp_zero]⟩
  invFun f := HomologicalComplex.mkHomFromSingle f.1 (fun k hk => by
    obtain rfl : k = 1 := by simpa using hk.symm
    exact f.2)
  left_inv φ := by
    apply HomologicalComplex.from_single_hom_ext
    dsimp only
    rw [HomologicalComplex.mkHomFromSingle_f, Iso.hom_inv_id_assoc]
  right_inv f := by
    apply Subtype.ext
    dsimp only
    rw [HomologicalComplex.mkHomFromSingle_f, Iso.inv_hom_id_assoc]

/-- Naturality of `singleHomEquiv` in the object: precomposing with `(single C 0).map u`
corresponds to composing with `u` on the degree `0` terms. -/
lemma singleHomEquiv_map {C : Type*} [Category C] [Preadditive C] [HasZeroObject C]
    {A B : C} (u : B ⟶ A) (K : CochainComplex C ℤ)
    (φ : (CochainComplex.singleFunctor C 0).obj A ⟶ K) :
    (singleHomEquiv B K ((CochainComplex.singleFunctor C 0).map u ≫ φ)).1 =
      u ≫ (singleHomEquiv A K φ).1 := by
  change (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 B).inv ≫
      ((CochainComplex.singleFunctor C 0).map u ≫ φ).f 0 =
    u ≫ (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 A).inv ≫ φ.f 0
  rw [HomologicalComplex.comp_f]
  change (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 B).inv ≫
      ((HomologicalComplex.single C (ComplexShape.up ℤ) 0).map u).f 0 ≫ φ.f 0 = _
  rw [HomologicalComplex.single_map_f_self]
  simp only [Category.assoc]
  rw [Iso.inv_hom_id_assoc]

/-- The universal property of a coproduct, for morphisms into a fixed object `W` which are killed
by a fixed morphism `d : W ⟶ W'`: they are the same as families of morphisms `X j ⟶ W` killed by
`d`. -/
def sigmaHomEquiv {C : Type*} [Category C] [HasZeroMorphisms C] {J : Type}
    (X : J → C) [HasCoproduct X] {W W' : C} (d : W ⟶ W') :
    {f : (∐X : C) ⟶ W // f ≫ d = 0} ≃ ∀ j, {f : X j ⟶ W // f ≫ d = 0} where
  toFun f j := ⟨Sigma.ι X j ≫ f.1, by rw [Category.assoc, f.2, Limits.comp_zero]⟩
  invFun g := ⟨Sigma.desc (fun j => (g j).1), by
    apply Sigma.hom_ext
    intro j
    rw [← Category.assoc, Sigma.ι_comp_desc, (g j).2, Limits.comp_zero]⟩
  left_inv f := by
    apply Subtype.ext
    apply Sigma.hom_ext
    intro j
    rw [Sigma.ι_comp_desc]
  right_inv g := by
    funext j
    apply Subtype.ext
    exact Sigma.ι_comp_desc (fun j => (g j).1) j

/-- The functor `CochainComplex.singleFunctor LightCondAb 0` (the cochain complex with `A` in
degree `0` and `0` elsewhere) preserves small coproducts, in the form: for every family
`A : J → LightCondAb` with a coproduct and every cochain complex `Z`, the map
`f ↦ (fun j => single.map (Sigma.ι A j) ≫ f)` out of `Hom (single (∐A)) Z` is a bijection. -/
theorem single_coproduct_bijective (J : Type) (A : J → LightCondAb)
    [CategoryTheory.Limits.HasCoproduct A] (Z : CochainComplex LightCondAb ℤ) :
    Function.Bijective (fun f : (CochainComplex.singleFunctor LightCondAb 0).obj (∐A) ⟶ Z =>
      fun j => (CochainComplex.singleFunctor LightCondAb 0).map
        (CategoryTheory.Limits.Sigma.ι A j) ≫ f) := by
  have key : ∀ (j : J) (f : (CochainComplex.singleFunctor LightCondAb 0).obj (∐A) ⟶ Z),
      (singleHomEquiv (A j) Z
          ((CochainComplex.singleFunctor LightCondAb 0).map (Sigma.ι A j) ≫ f)).1 =
        Sigma.ι A j ≫ (singleHomEquiv (∐A) Z f).1 := fun j f =>
    singleHomEquiv_map (Sigma.ι A j) Z f
  constructor
  · intro f₁ f₂ h
    have h1 : (singleHomEquiv (∐A) Z) f₁ = (singleHomEquiv (∐A) Z) f₂ := by
      apply Subtype.ext
      apply Sigma.hom_ext
      intro j
      rw [← key j f₁, ← key j f₂]
      exact congrArg Subtype.val (congrArg (singleHomEquiv (A j) Z) (congrFun h j))
    exact (singleHomEquiv (∐A) Z).injective h1
  · intro g
    refine ⟨(singleHomEquiv (∐A) Z).symm
      ((sigmaHomEquiv A (Z.d 0 1)).symm (fun j => (singleHomEquiv (A j) Z) (g j))), ?_⟩
    funext j
    apply (singleHomEquiv (A j) Z).injective
    apply Subtype.ext
    rw [key j]
    simp only [Equiv.apply_symm_apply]
    exact Sigma.ι_comp_desc (fun j => ((singleHomEquiv (A j) Z) (g j)).1) j

end

end Work.ANALYTIC
