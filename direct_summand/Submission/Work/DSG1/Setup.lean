import Mathlib
import ChallengeDeps
import Submission.Work.DSMap.Map
import Submission.Work.DSG1.Basic

/-!
# DSG1: infrastructure for the assembly of `Work.DSG1.comparison`

This file collects the small vocabulary shared by the assembly of the comparison map
`Work.DSG1.comparison` and by the lemmas delegated for it.

The single object `Σ_C M := DerivedCategory.Plus.singleFunctor C 0 |>.obj M` is the image of
`M ∈ C` under `single_0`; the one-term complex `singlePlusObj C M` is the corresponding
bounded below cochain complex.

Contents:

* `singlePlusObj`, and `singlePlusIso : Σ_C M ≅ Q (singlePlusObj C M)`;
* `mapSinglePlusIso`, the image of a one-term complex under an additive functor;
The bridge identifying the unit `rightDerivedFunctorPlusUnit'` of `ChallengeDeps` with the
complex level unit `Functor.rightDerivedFunctorPlusUnit` at the one-term complex is proved in
`Submission/Work/DSG1/rdfpuBridge.lean` (`Work.DSG1.rdfpuBridge`).
-/

open CategoryTheory AlgebraicGeometry Limits

universe u v w

namespace Work.DSG1

/-- The one-term complex `M[0]` (all terms but the degree `0` term are zero), as an object of
the category of bounded below cochain complexes. -/
noncomputable def singlePlusObj (C : Type*) [Category* C] [Preadditive C] [HasZeroObject C]
    (M : C) : CochainComplex.Plus C :=
  ⟨(CochainComplex.singleFunctor C 0).obj M, ⟨0, inferInstance⟩⟩

@[simp] lemma singlePlusObj_obj (C : Type*) [Category* C] [Preadditive C] [HasZeroObject C]
    (M : C) : (singlePlusObj C M).obj = (CochainComplex.singleFunctor C 0).obj M := rfl

/-- The canonical isomorphism `Σ_C M ≅ Q (singlePlusObj C M)` between the image of `M` under
`single_0` and the localization of the one-term complex of `M`. -/
noncomputable def singlePlusIso (C : Type*) [Category* C] [Abelian C] [HasDerivedCategory C]
    (M : C) : (DerivedCategory.Plus.singleFunctor C 0).obj M ≅
      (DerivedCategory.Plus.Q).obj (singlePlusObj C M) :=
  (ObjectProperty.fullyFaithfulι (DerivedCategory.TStructure.t.plus)).preimageIso
    ((DerivedCategory.Plus.singleFunctorιIso C 0).app M ≪≫
      (DerivedCategory.singleFunctorIsoCompQ C 0).app M ≪≫
        ((DerivedCategory.Plus.QCompιIso C).app (singlePlusObj C M)).symm)

/-- For an additive functor `F`, the image of the one-term complex of `M` under `F` is the
one-term complex of `F M`. -/
noncomputable def mapSinglePlusIso {C : Type*} [Category* C] [Abelian C] {D : Type*}
    [Category* D] [Abelian D] (F : C ⥤ D) [F.Additive] (M : C) :
    F.mapCochainComplexPlus.obj (singlePlusObj C M) ≅ singlePlusObj D (F.obj M) :=
  (ObjectProperty.fullyFaithfulι (CochainComplex.plus D)).preimageIso
    ((Functor.mapCochainComplexPlusCompι F).app (singlePlusObj C M) ≪≫
      (HomologicalComplex.singleMapHomologicalComplex F (ComplexShape.up ℤ) 0).app M)

end Work.DSG1
