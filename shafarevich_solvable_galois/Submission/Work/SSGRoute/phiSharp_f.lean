import Mathlib.Tactic.Have
import Mathlib.Combinatorics.Quiver.ReflQuiver
import Mathlib.CategoryTheory.Abelian.Projective.Extend
import Submission.Work.SSGRoute.MapExtAuxDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute

open CategoryTheory Limits

set_option backward.isDefEq.respectTransparency false

/-!
# Component computation for `phiSharp`

We prove that the cochain map `phiSharp F R R' φ` built from a chain map
`φ : R'.complex ⟶ F(R.complex)` (via `extendMap` and the canonical isomorphism
`extendFunctorIso` between `extend` and `F.mapHomologicalComplex`) agrees, in degree `-n`,
with `φ.f n` after identifying `(·.extend _).X (-n)` with `(·).X n`.

These are the elementary "unwinding" lemmas needed for `Work.SSGRoute.phiSharp_f`.
-/

section Helpers

variable {C : Type*} [Category C] [Abelian C] {D : Type*} [Category D] [Abelian D]

/-- The `o = some k` component of `extendFunctorIsoComp` (which is the identity on `some k`)
is compatible with `HomologicalComplex.extend.XIso`. -/
lemma extendFunctorIsoComp_natural (F : C ⥤ D) [F.Additive] (K : ChainComplex C ℕ)
    {o : Option ℕ} {k : ℕ} (hi : o = some k) :
    (extendFunctorIsoComp F K o).hom ≫
        F.map ((HomologicalComplex.extend.XIso K hi).hom)
      = (HomologicalComplex.extend.XIso
          ((F.mapHomologicalComplex (ComplexShape.down ℕ)).obj K) hi).hom := by
  subst hi
  simp only [HomologicalComplex.extend.XIso, HomologicalComplex.extend.X, extendFunctorIsoComp]
  rw [Iso.refl_hom, Category.id_comp, eqToIso.hom, eqToIso.hom, eqToHom_refl, F.map_id,
    eqToHom_refl]
  rfl

/-- The `(-n)`-component of `extendFunctorIso F K`, followed by `F.map` of the canonical
identification `(K.extend e).X (-n) ≅ K.X n`, equals the canonical identification
`((F(K)).extend e).X (-n) ≅ F(K).X n`. -/
lemma extendFunctorIso_comp_extendXIso (F : C ⥤ D) [F.Additive] (K : ChainComplex C ℕ)
    {i' : ℤ} {k : ℕ} (h : ComplexShape.embeddingDownNat.f k = i') :
    (extendFunctorIso F K).hom.f i' ≫
        F.map ((HomologicalComplex.extendXIso K ComplexShape.embeddingDownNat h).hom)
      = (HomologicalComplex.extendXIso
          ((F.mapHomologicalComplex (ComplexShape.down ℕ)).obj K)
          ComplexShape.embeddingDownNat h).hom := by
  rw [show (extendFunctorIso F K).hom.f i'
      = (extendFunctorIsoComp F K (ComplexShape.embeddingDownNat.r i')).hom from rfl]
  exact extendFunctorIsoComp_natural F K (ComplexShape.Embedding.r_eq_some _ h)

end Helpers

theorem phiSharp_f {C : Type*} [CategoryTheory.Category C] [CategoryTheory.Abelian C]
    {D : Type*} [CategoryTheory.Category D] [CategoryTheory.Abelian D]
    (F : CategoryTheory.Functor C D) [F.Additive]
    {X : C} (R : CategoryTheory.ProjectiveResolution X)
    {X' : D} (R' : CategoryTheory.ProjectiveResolution X')
    (φ : R'.complex ⟶ (F.mapHomologicalComplex (ComplexShape.down ℕ)).obj R.complex) (n : ℕ) :
    CategoryTheory.CategoryStruct.comp ((Work.SSGRoute.phiSharp F R R' φ).f (-↑n))
        (F.map ((R.cochainComplexXIso (-↑n) ↑n rfl).hom))
      = CategoryTheory.CategoryStruct.comp ((R'.cochainComplexXIso (-↑n) ↑n rfl).hom) (φ.f n) := by
  rw [Work.SSGRoute.phiSharp]
  simp only [HomologicalComplex.comp_f]
  rw [HomologicalComplex.extendMap_f φ ComplexShape.embeddingDownNat (i := n) (i' := -↑n)
    (by simp)]
  simp only [Category.assoc]
  simp only [CategoryTheory.ProjectiveResolution.cochainComplexXIso]
  have key : ∀ (h : ComplexShape.embeddingDownNat.f n = (-↑n : ℤ)),
      (extendFunctorIso F R.complex).hom.f (-↑n) ≫
          F.map (HomologicalComplex.extendXIso R.complex ComplexShape.embeddingDownNat h).hom
        = (HomologicalComplex.extendXIso
            ((F.mapHomologicalComplex (ComplexShape.down ℕ)).obj R.complex)
            ComplexShape.embeddingDownNat h).hom :=
    fun h => extendFunctorIso_comp_extendXIso F R.complex h
  rw [key]
  rw [Iso.inv_hom_id, Category.comp_id]

end Work.SSGRoute
