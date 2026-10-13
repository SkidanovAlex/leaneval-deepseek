import Mathlib
import Submission.Work.DSF1.Sheaf.AcyclicToolkit
import Submission.Work.DSF1.Sheaf.isIso_homologyMap_zero_mapHomologicalComplex

/-!
# The degree-`0` part of the unit of a right derived functor at a one-term complex

For an additive, left exact functor `F : C ⥤ D` between abelian categories, where `C` has enough
injectives, and an object `A : C`, the unit of the right derived functor
`F.rightDerivedFunctorPlusUnit` gives a morphism

`Q (F (A[0])) ⟶ RF (Q (A[0]))`

in the bounded below derived category of `D`.  This module proves that its image under the
`0`-th cohomology functor is an isomorphism:

`H⁰ (Q (F A)) = F A ⟶ H⁰ (RF (Q (A[0])))`

is the canonical comparison map `F A → R⁰ F (A)`, which is an isomorphism because `F` preserves
finite limits.

The proof is the classical one.  Choose a bounded below complex of injective objects `L` together
with a quasi-isomorphism `i : A[0] ⟶ L` (`CochainComplex.Plus.exists_quasiIso_injective`); the
unit of the right derived functor is an isomorphism at `L` (Mathlib's instance for the injective
derivability structure).  Naturality of the unit at `i` exhibits the unit at `A[0]` as a composite
of `Q (F i)`, the unit at `L`, and the inverse of `RF (Q i)`; the latter two become isomorphisms
after applying any functor, and the first one does after applying `H⁰` because `F` is left exact
and `i` is a quasi-isomorphism between complexes concentrated in degrees `≥ 0`
(the lemma `isIso_homologyMap_zero_mapHomologicalComplex`).
-/

namespace Work.DSF1.Sheaf

open CategoryTheory Limits

universe u v w x

set_option linter.style.haveILetI false

/-- The image under `H⁰` of the unit of the right derived functor `F.rightDerivedFunctorPlusUnit`
at the one-term complex `A[0]` is an isomorphism, for `F` additive and left exact. -/
theorem isIso_homology_zero_unit_single {C : Type u} [CategoryTheory.Category.{v} C]
    [CategoryTheory.Abelian C] [CategoryTheory.EnoughInjectives C]
    {D : Type w} [CategoryTheory.Category.{x} D] [CategoryTheory.Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    (F : CategoryTheory.Functor C D) [F.Additive]
    [CategoryTheory.Limits.PreservesFiniteLimits F] (A : C) :
    CategoryTheory.IsIso ((DerivedCategory.Plus.homologyFunctor D 0).map
      (F.rightDerivedFunctorPlusUnit.app (Work.DSF1.Sheaf.singlePlusObj C A))) := by
  -- `A[0]` is strictly supported in degrees `≥ 0`
  have hKge : (singlePlusObj C A).obj.IsStrictlyGE 0 := by
    change ((CochainComplex.singleFunctor C 0).obj A).IsStrictlyGE 0
    infer_instance
  haveI := hKge
  have hKge' : ((CochainComplex.Plus.ι C).obj (singlePlusObj C A)).IsStrictlyGE 0 := by
    change ((CochainComplex.singleFunctor C 0).obj A).IsStrictlyGE 0
    infer_instance
  haveI := hKge'
  -- a bounded below complex of injective objects quasi-isomorphic to `A[0]`
  obtain ⟨L, hL, i, hi⟩ := CochainComplex.Plus.exists_quasiIso_injective (singlePlusObj C A) 0
  let L₀ : CochainComplex.Plus C := (InjectiveObject.ι C).mapCochainComplexPlus.obj L
  -- the unit is an isomorphism at any bounded below complex of injectives
  have hL₀u : IsIso (F.rightDerivedFunctorPlusUnit.app L₀) := inferInstance
  -- and `Q i` is an isomorphism, `i` being a quasi-isomorphism
  have hQi : IsIso (DerivedCategory.Plus.Q.map i) := Localization.inverts _ _ _ hi
  -- naturality of the unit at `i`
  have nat : DerivedCategory.Plus.Q.map (F.mapCochainComplexPlus.map i) ≫
        F.rightDerivedFunctorPlusUnit.app L₀ =
      F.rightDerivedFunctorPlusUnit.app (singlePlusObj C A) ≫
        F.rightDerivedFunctorPlus.map (DerivedCategory.Plus.Q.map i) :=
    F.rightDerivedFunctorPlusUnit.naturality i
  -- hence the unit at `A[0]` is a composite of three maps
  have key : F.rightDerivedFunctorPlusUnit.app (singlePlusObj C A) =
      (DerivedCategory.Plus.Q.map (F.mapCochainComplexPlus.map i) ≫
        F.rightDerivedFunctorPlusUnit.app L₀) ≫
      CategoryTheory.inv (F.rightDerivedFunctorPlus.map (DerivedCategory.Plus.Q.map i)) := by
    rw [nat, Category.assoc, IsIso.hom_inv_id, Category.comp_id]
  rw [key, Functor.map_comp, Functor.map_comp]
  -- the first factor: `H⁰` of `Q (F i)`, which is `H⁰` of `F` applied to the quasi-isomorphism `i`
  have hA : IsIso ((DerivedCategory.Plus.homologyFunctor D 0).map
      (DerivedCategory.Plus.Q.map (F.mapCochainComplexPlus.map i))) := by
    -- the underlying map of complexes
    have hy : (CochainComplex.Plus.ι D).map (F.mapCochainComplexPlus.map i) =
        (F.mapHomologicalComplex (ComplexShape.up ℤ)).map ((CochainComplex.Plus.ι C).map i) := rfl
    have hiq : QuasiIso ((CochainComplex.Plus.ι C).map i) :=
      (CochainComplex.Plus.quasiIso_iff (C := C) i).mp hi
    have hLge' : ((CochainComplex.Plus.ι C).obj L₀).IsStrictlyGE 0 :=
      (CochainComplex.isStrictlyGE_mapHomologicalComplex_obj_iff L.obj (InjectiveObject.ι C) 0).mpr hL
    haveI := hLge'
    -- left exactness of `F` computes `H⁰ (F i)` as `F (H⁰ i)`
    have h1 : IsIso (HomologicalComplex.homologyMap
        ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map ((CochainComplex.Plus.ι C).map i)) 0) :=
      isIso_homologyMap_zero_mapHomologicalComplex F ((CochainComplex.Plus.ι C).map i)
    -- and `H⁰` on the derived category is `H⁰` of the underlying complex
    change IsIso ((DerivedCategory.Q ⋙ DerivedCategory.homologyFunctor D 0).map
      ((CochainComplex.Plus.ι D).map (F.mapCochainComplexPlus.map i)))
    rw [hy]
    exact (NatIso.isIso_map_iff (DerivedCategory.homologyFunctorFactors D 0) _).mpr h1
  haveI := hA
  haveI := hL₀u
  haveI := hQi
  -- a composite of isomorphisms
  simp only [Category.assoc]
  infer_instance

end Work.DSF1.Sheaf
