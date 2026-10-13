/-
Area DSCOH (curric-46) — vanishing of the negative cohomology of `RΓ(X, 𝒪_X)`.

For any scheme `X` over `Spec A`, the object `RΓ(X, 𝒪_X) = DSMap.RG A X f` lies in
`D⁺(A)`, and this file proves the stronger statement needed by `DSMap.area_COH`:
it lies in `D^{≥ 0}`, i.e. `Hⁱ(X, 𝒪_X) = 0` for `i < 0`.

The mathematical content is the standard computation of a right derived functor on a
complex concentrated in degree `0`: take a K-injective resolution `L` of `𝒪_X` which is
*strictly* supported in degrees `≥ 0`
(`DerivedCategory.Plus.exists_injective_nonempty_iso`, applied at `n = 0`), apply the
functor degreewise, and observe that the resulting complex still has vanishing terms in
negative degrees.  Since any additive functor sends a K-injective complex to a model of
the right derived functor (`Functor.rightDerivedFunctorPlusUnit` is an isomorphism on
complexes of injective objects), this computes `RΓ(X, 𝒪_X)` up to isomorphism as an
object of the derived category concentrated in degrees `≥ 0`.

The argument is carried out for an arbitrary additive functor between abelian categories
with enough injectives, because that is exactly the generality in which the computation
is true; the application to `Γ(X, -)` is then a one-liner.  Note that left exactness of
the functor is *not* used.
-/
import Mathlib
import Submission.Work.DSMap.Map

set_option linter.style.haveILetI false

namespace Work.DSCOH

open CategoryTheory Limits

/-- A functor preserving zero morphisms sends a complex strictly supported in degrees `≥ 0`
to a complex strictly supported in degrees `≥ 0`. -/
lemma mapCochainComplexPlus_isStrictlyGE {C D : Type*} [Category* C] [Category* D]
    [HasZeroMorphisms C] [HasZeroMorphisms D] (F : C ⥤ D) [F.PreservesZeroMorphisms]
    (K : CochainComplex.Plus C) [K.obj.IsStrictlyGE 0] :
    (F.mapCochainComplexPlus.obj K).obj.IsStrictlyGE 0 := by
  rw [CochainComplex.isStrictlyGE_iff]
  intro i hi
  rw [Functor.mapCochainComplexPlus_obj_obj]
  exact Functor.map_isZero _ (K.obj.isZero_of_isStrictlyGE 0 i hi)

/-- If `K` is a bounded below complex strictly supported in degrees `≥ 0`, then its image
under `F.mapCochainComplexPlus` is `≥ 0` in the bounded below derived category. -/
lemma Q_obj_mapCochainComplexPlus_isGE_zero {C D : Type*} [Category* C] [Category* D]
    [HasZeroMorphisms C] [Abelian D] [HasDerivedCategory D] (F : C ⥤ D)
    [F.PreservesZeroMorphisms] (K : CochainComplex.Plus C) [K.obj.IsStrictlyGE 0] :
    (DerivedCategory.Plus.Q.obj (F.mapCochainComplexPlus.obj K)).IsGE 0 := by
  haveI : (F.mapCochainComplexPlus.obj K).obj.IsStrictlyGE 0 :=
    mapCochainComplexPlus_isStrictlyGE F K
  haveI : (F.mapCochainComplexPlus.obj K).obj.IsGE 0 := inferInstance
  haveI hQ : ((CochainComplex.Plus.ι D ⋙ DerivedCategory.Q).obj
      (F.mapCochainComplexPlus.obj K)).IsGE 0 :=
    (DerivedCategory.isGE_Q_obj_iff (F.mapCochainComplexPlus.obj K).obj 0).mpr inferInstance
  have h1 : (DerivedCategory.Plus.ι.obj (DerivedCategory.Plus.Q.obj
      (F.mapCochainComplexPlus.obj K))).IsGE 0 :=
    (DerivedCategory.TStructure.t (C := D)).isGE_of_iso
      ((DerivedCategory.Plus.QCompιIso D).app (F.mapCochainComplexPlus.obj K)).symm 0
  exact (DerivedCategory.Plus.isGE_ι_obj_iff _ 0).mp h1

/-- **Right derived functors of an additive functor sit in nonnegative degrees on a
degree-`0` object.**  If `F : C ⥤ D` is additive between abelian categories and `C` has
enough injectives, then the right derived functor of the single complex with `Y` in
degree `0` lies in `D^{≥ 0}(D)`; equivalently `RⁱF(Y) = 0` for `i < 0`. -/
lemma rightDerivedFunctorPlus_single_isGE_zero {C D : Type*} [Category* C] [Category* D]
    [Abelian C] [Abelian D] [HasDerivedCategory C] [HasDerivedCategory D]
    (F : C ⥤ D) [F.Additive] [EnoughInjectives C] (Y : C) :
    (F.rightDerivedFunctorPlus.obj ((DerivedCategory.Plus.singleFunctor C 0).obj Y)).IsGE 0 := by
  obtain ⟨L, hL, ⟨e⟩⟩ := DerivedCategory.Plus.exists_injective_nonempty_iso
      ((DerivedCategory.Plus.singleFunctor C 0).obj Y) 0
  haveI := hL
  set K : CochainComplex.Plus C := (InjectiveObject.ι C).mapCochainComplexPlus.obj L with hK
  haveI : K.obj.IsStrictlyGE 0 := mapCochainComplexPlus_isStrictlyGE (InjectiveObject.ι C) L
  haveI hQ : (DerivedCategory.Plus.Q.obj (F.mapCochainComplexPlus.obj K)).IsGE 0 :=
    Q_obj_mapCochainComplexPlus_isGE_zero F K
  have e2 : F.rightDerivedFunctorPlus.obj
      ((DerivedCategory.Plus.singleFunctor C 0).obj Y) ≅
      DerivedCategory.Plus.Q.obj (F.mapCochainComplexPlus.obj K) :=
    F.rightDerivedFunctorPlus.mapIso e.symm ≪≫
      (asIso (F.rightDerivedFunctorPlusUnit.app K)).symm
  exact (DerivedCategory.Plus.TStructure.t (C := D)).isGE_of_iso e2.symm 0

theorem RG_homology_isZero_of_neg (A : Type*) [CommRing A]
    [HasDerivedCategory (ModuleCat A)] (X : AlgebraicGeometry.Scheme)
    (f : X ⟶ AlgebraicGeometry.Spec (CommRingCat.of A))
    [HasDerivedCategory (SheafOfModules X.ringCatSheaf)]
    [CategoryTheory.EnoughInjectives (SheafOfModules X.ringCatSheaf)] (i : ℤ) (hi : i < 0) :
    CategoryTheory.Limits.IsZero
      ((DerivedCategory.homologyFunctor (ModuleCat A) i).obj
        (DerivedCategory.Plus.ι.obj (DSMap.RG A X f))) := by
  have h : (DSMap.RG A X f).IsGE 0 :=
    rightDerivedFunctorPlus_single_isGE_zero (DSMap.GammaA A X f)
      (SheafOfModules.unit X.ringCatSheaf)
  haveI := h
  exact DerivedCategory.Plus.isZero_homology_of_isGE (DSMap.RG A X f) 0 i hi

end Work.DSCOH
