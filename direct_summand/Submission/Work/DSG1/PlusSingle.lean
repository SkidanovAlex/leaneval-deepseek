import Mathlib

/-!
# The single complex concentrated in one degree, as an object of `CochainComplex.Plus`

For an abelian category `C` and `n : ℤ`, `Work.DSG1.plusSingleComplex n : C ⥤ CochainComplex.Plus C`
is the functor sending `X : C` to the complex concentrated in degree `n`, regarded as a bounded
below complex.  Its essential property is that

`(DerivedCategory.Plus.singleFunctor C n).obj X = DerivedCategory.Plus.Q.obj
((plusSingleComplex n).obj X)`

*definitionally*, see `Work.DSG1.plusSingleFunctorIso`, and that the higher homology of the single
complex vanishes (`Work.DSG1.isZero_homology_singleFunctor`).
-/

namespace Work.DSG1

open CategoryTheory Limits

universe v u

section TheSingleComplexInPlus

variable {C : Type*} [Category* C] [Abelian C] (n : ℤ)

/-- The single complex concentrated in degree `n`, as an object of `CochainComplex.Plus C`. -/
noncomputable def plusSingleComplex : C ⥤ CochainComplex.Plus C :=
  ObjectProperty.lift _ (CochainComplex.singleFunctor C n) (fun X => ⟨n, inferInstance⟩)

@[simp]
lemma plusSingleComplex_obj_obj (X : C) :
    ((plusSingleComplex n).obj X).obj = (CochainComplex.singleFunctor C n).obj X := rfl

variable {n} [HasDerivedCategory C]

/-- The single functor into the bounded below derived category is the composite of the single
complex with the localization functor `DerivedCategory.Plus.Q`. -/
noncomputable def plusSingleFunctorIso (X : C) :
    (DerivedCategory.Plus.singleFunctor C n).obj X ≅
      DerivedCategory.Plus.Q.obj ((plusSingleComplex (C := C) n).obj X) :=
  ObjectProperty.isoMk _ (Iso.refl _)

end TheSingleComplexInPlus

section HomologyTheSingleComplex

variable {C : Type*} [Category* C] [Abelian C] (X : C)

/-- The single complex has vanishing homology away from its degree. -/
lemma isZero_homology_singleFunctor (q : ℤ) (hq : q ≠ 0) :
    IsZero ((CochainComplex.singleFunctor C 0).obj X |>.homology q) :=
  HomologicalComplex.isZero_single_obj_homology (ComplexShape.up ℤ) 0 X q hq

end HomologyTheSingleComplex

section HomologyIso

open DerivedCategory

variable {D : Type*} [Category* D] [Abelian D] [HasDerivedCategory D]

/-- The degree-`q` homology of `Plus.Q.obj K` is the degree-`q` homology of the underlying
complex `K`. -/
noncomputable def plusQHomologyIso (q : ℤ) :
    DerivedCategory.Plus.Q ⋙ DerivedCategory.Plus.homologyFunctor D q ≅
      CochainComplex.Plus.ι D ⋙ HomologicalComplex.homologyFunctor D (ComplexShape.up ℤ) q :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerLeft (CochainComplex.Plus.ι D)
      (DerivedCategory.homologyFunctorFactors D q)

/-- `H^0` of the single object at `0` is the identity: passing to the single object concentrated in
degree `0` in the bounded below derived category and then taking `H^0` is naturally isomorphic to
the identity. -/
noncomputable def plusSingleHomologyIso :
    ((plusSingleComplex (C := D) 0 ⋙ DerivedCategory.Plus.Q) ⋙
        (DerivedCategory.Plus.homologyFunctor D 0)) ≅ 𝟭 D :=
  (Functor.associator _ _ _) ≪≫
    Functor.isoWhiskerLeft (plusSingleComplex (C := D) 0) (plusQHomologyIso (D := D) 0) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    HomologicalComplex.homologyFunctorSingleIso D (ComplexShape.up ℤ) 0

/-- The same statement, with the single functor spelled using `DerivedCategory.Plus.singleFunctor`
(it is definitionally the composite `plusSingleComplex 0 ⋙ Plus.Q`). -/
noncomputable def plusSingleFunctorHomologyIso :
    (DerivedCategory.Plus.singleFunctor D 0) ⋙
      (DerivedCategory.Plus.homologyFunctor D 0) ≅ 𝟭 D :=
  plusSingleHomologyIso (D := D)

end HomologyIso

end Work.DSG1
