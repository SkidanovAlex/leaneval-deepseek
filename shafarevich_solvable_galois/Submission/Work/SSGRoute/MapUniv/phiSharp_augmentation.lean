import Mathlib.Tactic.Have
import Mathlib.Combinatorics.Quiver.ReflQuiver
import Mathlib.CategoryTheory.Abelian.Projective.Extend
import Submission.Work.SSGRoute.MapUnivDefs
import Submission.Work.SSGRoute.phiSharp_f
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Augmentation compatibility of `phiSharp`

Let `F : C ⥤ D` be an additive functor between abelian categories which preserves finite
limits and finite colimits, `R` a projective resolution of `X : C` and `R'` a projective
resolution of `X' : D`.  Given a chain map `φ : R'.complex ⟶ F(R.complex)` which is
compatible with the augmentations (`hφ`), the induced cochain map
`phiSharp F R R' φ : R'.cochainComplex ⟶ F(R.cochainComplex)` is compatible with the
integer-indexed augmentations `R'.π'` and `R.π'`.

The proof is a degree-zero computation.  By `HomologicalComplex.to_single_hom_ext` it
suffices to compare the components in degree `0`; there `R.π'` and `R'.π'` unfold
(`ProjectiveResolution.π'_f_zero`) into `cochainComplexXIso` composed with the
chain-level augmentation and the single-object comparison isomorphisms, and the
`singleMapHomologicalComplex` components cancel against them.  The chain-level input is
the degree-`0` component of `hφ`.

Note the `set_option` below: the objects `((HomologicalComplex.single V c j).obj A).X j`
are only *propositionally* equal to `A` for the indexing shapes `ComplexShape.up ℤ`
(whereas they are equal by `rfl` for `down ℕ`), so several rewrites need definitional
equality up to full unfolding.
-/

open CategoryTheory Limits

namespace Work.SSGRoute.MapUniv

set_option maxHeartbeats 1000000

set_option backward.isDefEq.respectTransparency false in
theorem phiSharp_augmentation {C : Type*} [CategoryTheory.Category C] [CategoryTheory.Abelian C]
    {D : Type*} [CategoryTheory.Category D] [CategoryTheory.Abelian D]
    (F : CategoryTheory.Functor C D) [F.Additive]
    [CategoryTheory.Limits.PreservesFiniteLimits F]
    [CategoryTheory.Limits.PreservesFiniteColimits F]
    {X : C} (R : CategoryTheory.ProjectiveResolution X)
    {X' : D} (R' : CategoryTheory.ProjectiveResolution X') (g' : X' ⟶ F.obj X)
    (φ : R'.complex ⟶ (F.mapHomologicalComplex (ComplexShape.down ℕ)).obj R.complex)
    (hφ : CategoryTheory.CategoryStruct.comp φ
        (CategoryTheory.CategoryStruct.comp
          ((F.mapHomologicalComplex (ComplexShape.down ℕ)).map R.π)
          ((HomologicalComplex.singleMapHomologicalComplex F (ComplexShape.down ℕ) 0).hom.app X))
        = CategoryTheory.CategoryStruct.comp R'.π ((ChainComplex.single₀ D).map g')) :
    CategoryTheory.CategoryStruct.comp (Work.SSGRoute.MapUniv.phiSharp F R R' φ)
        (CategoryTheory.CategoryStruct.comp
          ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map R.π')
          ((HomologicalComplex.singleMapHomologicalComplex F (ComplexShape.up ℤ) 0).hom.app X))
      = CategoryTheory.CategoryStruct.comp R'.π' ((CochainComplex.singleFunctor D 0).map g') := by
  have hz : -(↑(0:ℕ)) = (0:ℤ) := by lia
  -- Components of the `singleMapHomologicalComplex` isomorphisms.
  have hsmUp : ((HomologicalComplex.singleMapHomologicalComplex F (ComplexShape.up ℤ) 0).hom.app X).f 0
      = F.map (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 X).hom ≫
        (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 (F.obj X)).inv :=
    HomologicalComplex.singleMapHomologicalComplex_hom_app_self F (ComplexShape.up ℤ) 0 X
  have hsmDown : ((HomologicalComplex.singleMapHomologicalComplex F (ComplexShape.down ℕ) 0).hom.app X).f 0
      = F.map (HomologicalComplex.singleObjXSelf (ComplexShape.down ℕ) 0 X).hom ≫
        (HomologicalComplex.singleObjXSelf (ComplexShape.down ℕ) 0 (F.obj X)).inv :=
    HomologicalComplex.singleMapHomologicalComplex_hom_app_self F (ComplexShape.down ℕ) 0 X
  have hg'map : ((CochainComplex.singleFunctor D 0).map g').f 0
      = (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 X').hom ≫ g' ≫
        (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 (F.obj X)).inv := by
    change ((HomologicalComplex.single D (ComplexShape.up ℤ) 0).map g').f 0 = _
    rw [HomologicalComplex.single_map_f_self]
  -- Degree-zero components of the augmentations.
  have hπR : R.π'.f 0 = (R.cochainComplexXIso 0 0 hz).hom ≫ R.π.f 0 ≫
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 X).inv :=
    CategoryTheory.ProjectiveResolution.π'_f_zero R
  have hπR' : R'.π'.f 0 = (R'.cochainComplexXIso 0 0 hz).hom ≫ R'.π.f 0 ≫
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 X').inv :=
    CategoryTheory.ProjectiveResolution.π'_f_zero R'
  -- Degree-zero component of the hypothesis `hφ`.
  have key3 : φ.f 0 ≫ F.map (R.π.f 0) = R'.π.f 0 ≫ g' := by
    have h := HomologicalComplex.congr_hom hφ 0
    simp only [HomologicalComplex.comp_f, CategoryTheory.Functor.mapHomologicalComplex_map_f,
      ChainComplex.single₀_map_f_zero] at h
    rw [hsmDown] at h
    simp only [ChainComplex.single₀ObjXSelf, Iso.refl_hom, Iso.refl_inv,
      CategoryTheory.Functor.map_id, Category.id_comp] at h
    have hcomp : φ.f 0 ≫ (F.map (R.π.f 0) ≫ 𝟙 _) = φ.f 0 ≫ F.map (R.π.f 0) := by
      rw [Category.comp_id]
    exact hcomp.symm.trans h
  -- The degree-zero component of `phiSharp`.
  have keyR : (Work.SSGRoute.MapUniv.phiSharp F R R' φ).f 0 ≫
      F.map ((R.cochainComplexXIso 0 0 hz).hom)
      = (R'.cochainComplexXIso 0 0 hz).hom ≫ φ.f 0 := by
    have h := Work.SSGRoute.phiSharp_f F R R' φ 0
    rw [show Work.SSGRoute.phiSharp F R R' φ = Work.SSGRoute.MapUniv.phiSharp F R R' φ from rfl] at h
    exact h
  -- The same, in a form adapted to composition on the right.
  have keyR4 : ∀ {Y : C} {W : D} (ψ : R.complex.X 0 ⟶ Y)
      (χ : F.obj Y ⟶ W),
      (Work.SSGRoute.MapUniv.phiSharp F R R' φ).f 0 ≫
          F.map ((R.cochainComplexXIso 0 0 hz).hom ≫ ψ) ≫ χ
        = (R'.cochainComplexXIso 0 0 hz).hom ≫ φ.f 0 ≫ F.map ψ ≫ χ := by
    intro Y W ψ χ
    simp only [CategoryTheory.Functor.map_comp, ← Category.assoc]
    rw [keyR]
  -- Cancellation of the single-object comparison isomorphisms of `up ℤ`.
  have hcancel2 : F.map (R.π.f 0 ≫ (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 X).inv) ≫
      F.map (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 X).hom ≫
        (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 (F.obj X)).inv
      = F.map (R.π.f 0) ≫
        (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 (F.obj X)).inv := by
    rw [← Category.assoc, ← CategoryTheory.Functor.map_comp, Category.assoc, Iso.inv_hom_id,
      Category.comp_id]
  have key3s : φ.f 0 ≫ F.map (R.π.f 0) ≫
        (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 (F.obj X)).inv
      = R'.π.f 0 ≫ g' ≫
        (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 (F.obj X)).inv := by
    rw [← Category.assoc, key3, Category.assoc]
  -- Left hand side, in degree `0`.
  have hL : (Work.SSGRoute.MapUniv.phiSharp F R R' φ ≫
        (F.mapHomologicalComplex (ComplexShape.up ℤ)).map R.π' ≫
          (HomologicalComplex.singleMapHomologicalComplex F (ComplexShape.up ℤ) 0).hom.app X).f 0
      = (R'.cochainComplexXIso 0 0 hz).hom ≫ R'.π.f 0 ≫ g' ≫
        (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 (F.obj X)).inv := by
    simp only [HomologicalComplex.comp_f]
    rw [CategoryTheory.Functor.mapHomologicalComplex_map_f]
    rw [hπR]
    rw [hsmUp]
    rw [keyR4]
    rw [hcancel2]
    rw [key3s]
  -- Right hand side, in degree `0`.
  have hR : (R'.π' ≫ (CochainComplex.singleFunctor D 0).map g').f 0
      = (R'.cochainComplexXIso 0 0 hz).hom ≫ R'.π.f 0 ≫ g' ≫
        (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 (F.obj X)).inv := by
    rw [HomologicalComplex.comp_f]
    rw [hπR']
    rw [hg'map]
    rw [Category.assoc]
    rw [Category.assoc]
    rw [Iso.inv_hom_id_assoc]
  apply HomologicalComplex.to_single_hom_ext
  rw [hL, hR]

end Work.SSGRoute.MapUniv
