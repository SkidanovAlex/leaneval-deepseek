import Mathlib
import Submission.Work.DSG1.Setup

namespace Work.DSG1

open CategoryTheory

universe u v

/-
**The canonical isomorphism `mapSinglePlusIso` is compatible with composition.**

For additive functors `F₁ : C ⥤ D` and `F₂ : D ⥤ E`, the isomorphism
`mapSinglePlusIso F : F.mapCochainComplexPlus.obj (singlePlusObj C M) ≅ singlePlusObj D (F M)`
(from `Submission.Work.DSG1.Setup`) satisfies, in the inverse direction, the composition
compatibility used in the assembly of `Work.DSG1.comparison`:
`(mapSinglePlusIso F₂ (F₁ M)).inv ≫ F₂.mapCochainComplexPlus.map ((mapSinglePlusIso F₁ M).inv)
= (mapSinglePlusIso (F₁ ⋙ F₂) M).inv`.

Suggested proof: unfold `mapSinglePlusIso` (the `mapCochainComplexPlusCompι` factor is
`Iso.refl _`), apply `CategoryTheory.ObjectProperty.hom_ext` (or the `FullyFaithful` API for
`CochainComplex.Plus.ι`, which is faithful) and `HomologicalComplex.ext`/`ext i`, reducing the
statement to the `i`-th component of Mathlib's
`HomologicalComplex.singleMapHomologicalComplex_comp_inv_app` (the degree `0` component is then the
identity, the other components are zero).  The `by rfl` shortcut does *not* work.
-/

/-- The inverse of `mapSinglePlusIso F M`, seen as a morphism of the underlying cochain complexes,
is the inverse of Mathlib's canonical isomorphism `singleMapHomologicalComplex F (up ℤ) 0` at `M`.
This is the "component computation" of `mapSinglePlusIso`: the factor
`mapCochainComplexPlusCompι F` in its definition is the identity, and `ObjectProperty.fullyFaithfulι`
does not change the underlying morphism of complexes. -/
lemma mapSinglePlusIso_inv_hom {C : Type*} [Category* C] [Abelian C] {D : Type*} [Category* D]
    [Abelian D] (F : C ⥤ D) [F.Additive] (M : C) :
    (mapSinglePlusIso F M).inv.hom =
      (HomologicalComplex.singleMapHomologicalComplex F (ComplexShape.up ℤ) 0).inv.app M := by
  have h1 : (mapSinglePlusIso F M).inv.hom =
      ((Functor.mapCochainComplexPlusCompι F).app (singlePlusObj C M) ≪≫
        (HomologicalComplex.singleMapHomologicalComplex F (ComplexShape.up ℤ) 0).app M).inv := rfl
  have h2 : ((Functor.mapCochainComplexPlusCompι F).app (singlePlusObj C M) ≪≫
        (HomologicalComplex.singleMapHomologicalComplex F (ComplexShape.up ℤ) 0).app M).inv =
      ((HomologicalComplex.singleMapHomologicalComplex F (ComplexShape.up ℤ) 0).app M).inv ≫
        ((Functor.mapCochainComplexPlusCompι F).app (singlePlusObj C M)).inv :=
    Iso.trans_inv _ _
  have h3 : ((Functor.mapCochainComplexPlusCompι F).app (singlePlusObj C M)).inv = 𝟙 _ := by
    rw [Iso.app_inv, Functor.mapCochainComplexPlusCompι_inv_app]
    rfl
  exact h1.trans (h2.trans (Category.comp_id _))

theorem mapSinglePlusComp {C : Type*} [Category* C] [Abelian C] {D : Type*} [Category* D]
    [Abelian D] {E : Type*} [Category* E] [Abelian E] (F₁ : C ⥤ D) [F₁.Additive]
    (F₂ : D ⥤ E) [F₂.Additive] (M : C) :
    (Work.DSG1.mapSinglePlusIso F₂ (F₁.obj M)).inv ≫
        F₂.mapCochainComplexPlus.map ((Work.DSG1.mapSinglePlusIso F₁ M).inv) =
      (Work.DSG1.mapSinglePlusIso (F₁ ⋙ F₂) M).inv := by
  apply ObjectProperty.hom_ext
  have hL : ((mapSinglePlusIso F₂ (F₁.obj M)).inv ≫
      F₂.mapCochainComplexPlus.map ((mapSinglePlusIso F₁ M).inv)).hom =
      (mapSinglePlusIso F₂ (F₁.obj M)).inv.hom ≫
        (F₂.mapCochainComplexPlus.map ((mapSinglePlusIso F₁ M).inv)).hom := rfl
  have hA : (mapSinglePlusIso F₂ (F₁.obj M)).inv.hom =
      (HomologicalComplex.singleMapHomologicalComplex F₂ (ComplexShape.up ℤ) 0).inv.app
        (F₁.obj M) :=
    mapSinglePlusIso_inv_hom F₂ (F₁.obj M)
  have hB : (F₂.mapCochainComplexPlus.map ((mapSinglePlusIso F₁ M).inv)).hom =
      (F₂.mapHomologicalComplex (ComplexShape.up ℤ)).map
        ((HomologicalComplex.singleMapHomologicalComplex F₁ (ComplexShape.up ℤ) 0).inv.app M) :=
    (Functor.mapCochainComplexPlus_map_hom F₂ _).trans
      (congrArg _ (mapSinglePlusIso_inv_hom F₁ M))
  have hPQ : (mapSinglePlusIso F₂ (F₁.obj M)).inv.hom ≫
        (F₂.mapCochainComplexPlus.map ((mapSinglePlusIso F₁ M).inv)).hom =
      (HomologicalComplex.singleMapHomologicalComplex F₂ (ComplexShape.up ℤ) 0).inv.app (F₁.obj M) ≫
        (F₂.mapHomologicalComplex (ComplexShape.up ℤ)).map
          ((HomologicalComplex.singleMapHomologicalComplex F₁ (ComplexShape.up ℤ) 0).inv.app M) :=
    congrArg₂ (fun a b => a ≫ b) hA hB
  exact (hL.trans hPQ).trans ((HomologicalComplex.singleMapHomologicalComplex_comp_inv_app
    F₁ F₂ (ComplexShape.up ℤ) 0 M).symm.trans (mapSinglePlusIso_inv_hom (F₁ ⋙ F₂) M).symm)

end Work.DSG1
