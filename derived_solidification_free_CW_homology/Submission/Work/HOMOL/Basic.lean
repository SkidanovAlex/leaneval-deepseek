import Mathlib
import ChallengeDeps

/-!
# AREA HOMOL — general homological algebra inputs (holes 11–12)

This file contains the two general results about homology functors that the CW comparison
of `REFS/05 §4` needs:

* `Work.HOMOL.mapHomologicalComplexHomologyIso` — for a functor `F : C₁ ⤳ C₂` between abelian
  categories which preserves kernels and cokernels (i.e. `F.PreservesHomology`), the `i`-th
  homology of the degreewise image of a complex `K` is `F` of the `i`-th homology of `K`,
  naturally in `K`.
* `Work.HOMOL.mapDerivedCategoryHomologyIso` — the same statement on derived categories:
  `F.mapDerivedCategory ⋙ homologyFunctor C₂ n ≅ homologyFunctor C₁ n ⋙ F`.

The second is the formal content of "the derived inclusion `ι_D` commutes with homology"
(`REFS/05 §4`, first bullet), applied to `F := isSolid.ι`, which is exact
(`LightCondensed.Solid.PreservesFiniteLimits` / `PreservesFiniteColimits` in `ChallengeDeps`).

Everything here is pure homological algebra: no condensed mathematics.
-/

noncomputable section

open CategoryTheory Limits

namespace Work.HOMOL

universe v₁ v₂ v₃ u₁ u₂ u₃

variable {C₁ : Type u₁} [Category.{v₁} C₁] [Abelian C₁]
  {C₂ : Type u₂} [Category.{v₂} C₂] [Abelian C₂]

/-- **Exact functors commute with homology of complexes.**
If `F : C₁ ⤳ C₂` preserves kernels and cokernels, then the `i`-th homology of `F` applied
degreewise to a complex `K` is `F` of the `i`-th homology of `K`, naturally in `K`.

The isomorphism is assembled from `HomologicalComplex.homologyFunctorIso` (homology of a
complex = homology of its `sc` short complex) and `ShortComplex.homologyFunctorIso`
(homology of a short complex commutes with an exact functor); the remaining steps are
reassociations of functor composition. -/
noncomputable def mapHomologicalComplexHomologyIso {ι : Type u₃} (c : ComplexShape ι)
    (F : C₁ ⥤ C₂) [F.PreservesZeroMorphisms] [F.PreservesHomology] (i : ι) :
    F.mapHomologicalComplex c ⋙ HomologicalComplex.homologyFunctor C₂ c i ≅
      HomologicalComplex.homologyFunctor C₁ c i ⋙ F :=
  (Functor.isoWhiskerLeft (F.mapHomologicalComplex c)
      (HomologicalComplex.homologyFunctorIso C₂ c i) :
      _ ≅ F.mapHomologicalComplex c ⋙ (HomologicalComplex.shortComplexFunctor C₂ c i ⋙
        ShortComplex.homologyFunctor C₂)) ≪≫
  ((Functor.associator (F.mapHomologicalComplex c) (HomologicalComplex.shortComplexFunctor C₂ c i)
      (ShortComplex.homologyFunctor C₂)).symm :
      (F.mapHomologicalComplex c ⋙ (HomologicalComplex.shortComplexFunctor C₂ c i ⋙
        ShortComplex.homologyFunctor C₂)) ≅
      ((F.mapHomologicalComplex c ⋙ HomologicalComplex.shortComplexFunctor C₂ c i) ⋙
        ShortComplex.homologyFunctor C₂)) ≪≫
  (Functor.isoWhiskerRight (eqToIso (rfl : F.mapHomologicalComplex c ⋙
      HomologicalComplex.shortComplexFunctor C₂ c i =
        HomologicalComplex.shortComplexFunctor C₁ c i ⋙ F.mapShortComplex))
      (ShortComplex.homologyFunctor C₂)) ≪≫
  (Functor.associator (HomologicalComplex.shortComplexFunctor C₁ c i) F.mapShortComplex
      (ShortComplex.homologyFunctor C₂)) ≪≫
  (Functor.isoWhiskerLeft (HomologicalComplex.shortComplexFunctor C₁ c i)
      (ShortComplex.homologyFunctorIso F)) ≪≫
  ((Functor.associator (HomologicalComplex.shortComplexFunctor C₁ c i)
      (ShortComplex.homologyFunctor C₁) F).symm) ≪≫
  (Functor.isoWhiskerRight (HomologicalComplex.homologyFunctorIso C₁ c i).symm F)

/-- Pointwise form of `mapHomologicalComplexHomologyIso`: the `i`-th homology of the degreewise
image of a single complex. -/
noncomputable def mapHomologicalComplexHomologyIso_app {ι : Type u₃} (c : ComplexShape ι)
    (F : C₁ ⥤ C₂) [F.PreservesZeroMorphisms] [F.PreservesHomology] (i : ι)
    (K : HomologicalComplex C₁ c) :
    ((F.mapHomologicalComplex c).obj K).homology i ≅ F.obj (K.homology i) :=
  (mapHomologicalComplexHomologyIso c F i).app K

variable [HasDerivedCategory.{v₃} C₁] [HasDerivedCategory.{v₃} C₂]

/-- **Exact functors between abelian categories commute with homology on derived categories.**
For an exact functor `F : C₁ ⤳ C₂`, `F.mapDerivedCategory ⋙ homologyFunctor C₂ n` is naturally
isomorphic to `homologyFunctor C₁ n ⋙ F`.

The isomorphism is produced by the universal property of the localisation: it is the lift along
`DerivedCategory.Q` of the isomorphism of precomposed functors obtained from
`Functor.mapDerivedCategoryFactors` (relating `Q ⋙ F.mapDerivedCategory` to
`F.mapHomologicalComplex ⋙ Q`), `DerivedCategory.homologyFunctorFactors` (relating
`Q ⋙ homologyFunctor` to the homology functor on complexes) and
`mapHomologicalComplexHomologyIso`. -/
noncomputable def mapDerivedCategoryHomologyIso (F : C₁ ⥤ C₂) [F.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F] (n : ℤ) :
    F.mapDerivedCategory ⋙ DerivedCategory.homologyFunctor C₂ n ≅
      DerivedCategory.homologyFunctor C₁ n ⋙ F :=
  Localization.liftNatIso DerivedCategory.Q (HomologicalComplex.quasiIso C₁ (ComplexShape.up ℤ))
    (DerivedCategory.Q ⋙ F.mapDerivedCategory ⋙ DerivedCategory.homologyFunctor C₂ n)
    (DerivedCategory.Q ⋙ (DerivedCategory.homologyFunctor C₁ n ⋙ F))
    (F.mapDerivedCategory ⋙ DerivedCategory.homologyFunctor C₂ n)
    (DerivedCategory.homologyFunctor C₁ n ⋙ F)
    (((Functor.associator (DerivedCategory.Q) F.mapDerivedCategory
        (DerivedCategory.homologyFunctor C₂ n)).symm) ≪≫
     (Functor.isoWhiskerRight F.mapDerivedCategoryFactors
        (DerivedCategory.homologyFunctor C₂ n)) ≪≫
     (Functor.associator (F.mapHomologicalComplex (ComplexShape.up ℤ)) (DerivedCategory.Q)
        (DerivedCategory.homologyFunctor C₂ n)) ≪≫
     (Functor.isoWhiskerLeft (F.mapHomologicalComplex (ComplexShape.up ℤ))
        (DerivedCategory.homologyFunctorFactors C₂ n)) ≪≫
     (mapHomologicalComplexHomologyIso (ComplexShape.up ℤ) F n) ≪≫
     (Functor.isoWhiskerRight (DerivedCategory.homologyFunctorFactors C₁ n).symm F) ≪≫
     ((Functor.associator (DerivedCategory.Q) (DerivedCategory.homologyFunctor C₁ n) F).symm))

/-- Pointwise form of `mapDerivedCategoryHomologyIso`. -/
noncomputable def mapDerivedCategoryHomologyIso_app (F : C₁ ⥤ C₂) [F.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F] (n : ℤ) (K : DerivedCategory C₁) :
    (DerivedCategory.homologyFunctor C₂ n).obj (F.mapDerivedCategory.obj K) ≅
      F.obj ((DerivedCategory.homologyFunctor C₁ n).obj K) :=
  (mapDerivedCategoryHomologyIso F n).app K

end Work.HOMOL
