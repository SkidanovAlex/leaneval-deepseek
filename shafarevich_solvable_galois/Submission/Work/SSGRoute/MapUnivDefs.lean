import Mathlib.Combinatorics.Quiver.ReflQuiver
import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexSingle
import Mathlib.CategoryTheory.Abelian.Projective.Extend
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Self-contained definitions for the "L–M" lemma `mapExtAddHom_extMk_univ`

An additive functor `F : C ⥤ D` commuting with `HomologicalComplex.extend` along
`ComplexShape.embeddingDownNat`, and the induced cochain map `MapUniv.phiSharp` on `ℤ`-indexed
complexes.  Kept in its own namespace `Work.SSGRoute.MapUniv` so that it does not collide with
the (concurrently edited) `Work.SSGRoute.phiSharp`.
-/

open CategoryTheory Limits

universe u v

namespace Work.SSGRoute.MapUniv

variable {C : Type u} [Category.{v} C] [Abelian C] {D : Type*} [Category D] [Abelian D]

/-- The components of the canonical isomorphism expressing that the extension along
`ComplexShape.embeddingDownNat` commutes with an additive functor. -/
noncomputable def extendFunctorIsoComp (F : C ⥤ D) [F.Additive] (K : ChainComplex C ℕ)
    (o : Option ℕ) :
    HomologicalComplex.extend.X ((F.mapHomologicalComplex (ComplexShape.down ℕ)).obj K) o ≅
    F.obj (HomologicalComplex.extend.X K o) :=
  match o with
  | none => (HomologicalComplex.extend.isZero_X ((F.mapHomologicalComplex (ComplexShape.down ℕ)).obj K)
        (rfl : (none : Option ℕ) = none)).iso
      (Functor.map_isZero F (HomologicalComplex.extend.isZero_X K (rfl : (none : Option ℕ) = none)))
  | some k =>
      Iso.refl _

/-- The extension along `ComplexShape.embeddingDownNat` commutes with an additive functor. -/
noncomputable def extendFunctorIso (F : C ⥤ D) [F.Additive] (K : ChainComplex C ℕ) :
    (((F.mapHomologicalComplex (ComplexShape.down ℕ)).obj K).extend ComplexShape.embeddingDownNat) ≅
    ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj (K.extend ComplexShape.embeddingDownNat)) :=
  HomologicalComplex.Hom.isoOfComponents
    (fun i' => extendFunctorIsoComp F K (ComplexShape.embeddingDownNat.r i')) (by
    intro i j hij
    dsimp only [HomologicalComplex.extend, CategoryTheory.Functor.mapHomologicalComplex_obj_d]
    have key2 : ∀ (o₁ o₂ : Option ℕ),
        (extendFunctorIsoComp F K o₁).hom ≫ F.map (HomologicalComplex.extend.d K o₁ o₂) =
          HomologicalComplex.extend.d ((F.mapHomologicalComplex (ComplexShape.down ℕ)).obj K) o₁ o₂ ≫
            (extendFunctorIsoComp F K o₂).hom := by
      intro o₁ o₂
      cases o₁ <;> cases o₂ <;>
        dsimp only [extendFunctorIsoComp, HomologicalComplex.extend.d]
      all_goals try rw [Iso.refl_hom]
      all_goals try rw [CategoryTheory.Functor.mapHomologicalComplex_obj_d]
      all_goals try rw [Functor.map_zero]
      all_goals try erw [Limits.comp_zero]
      all_goals try erw [Limits.zero_comp]
      all_goals try erw [Category.id_comp]
      all_goals try erw [Category.comp_id]
      all_goals try rfl
    exact key2 _ _)

/-- The cochain map on `ℤ`-indexed complexes induced by a chain map `φ` into `F(R.complex)`. -/
noncomputable def phiSharp (F : C ⥤ D) [F.Additive] {X : C} (R : ProjectiveResolution X)
    {X' : D} (R' : ProjectiveResolution X')
    (φ : R'.complex ⟶ (F.mapHomologicalComplex (ComplexShape.down ℕ)).obj R.complex) :
    R'.cochainComplex ⟶ (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj R.cochainComplex :=
  HomologicalComplex.extendMap φ ComplexShape.embeddingDownNat ≫
    (extendFunctorIso F R.complex).hom


/-- The degree-`n` morphism of cochain complexes `R.cochainComplex ⟶ single Y ⟦n⟧` whose
`equivHomShift`-image is the cocycle defining `R.extMk g`. -/
noncomputable def extMkShiftedHom {C : Type u} [Category.{v} C] [Abelian C]
    {X Y : C} (R : ProjectiveResolution X) {n : ℕ}
    (g : R.complex.X n ⟶ Y) (hg : R.complex.d (n + 1) n ≫ g = 0) :
    CategoryTheory.ShiftedHom R.cochainComplex ((CochainComplex.singleFunctor C 0).obj Y) ((n : ℤ)) :=
  CochainComplex.HomComplex.Cocycle.equivHomShift.symm
    (CochainComplex.HomComplex.Cocycle.toSingleMk
      ((R.cochainComplexXIso (-↑n) n rfl).hom ≫ g) (by simp) (-↑(n+1)) (by lia)
      (by simpa [R.cochainComplex_d (-(↑n+1)) (-↑n) (n+1) n (by simp) rfl, hg]))

end Work.SSGRoute.MapUniv
