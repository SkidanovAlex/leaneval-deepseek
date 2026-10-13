import Mathlib
import Submission.Work.DSMap.Map
import Submission.Work.DSG4a.Criterion

/-!
# DSG4a: the interface with the frozen area `F1` (Čech model of `RΓ`)

The area `F1` of the proof map (`DSMap.area_F1_cech`, frozen) provides, for `f : X ⟶ Spec A`
separated and quasi-compact and a finite affine cover `U`, a cochain complex `cechZ A X f U`
and an isomorphism in the derived category `e : ι(RΓ(X, 𝒪)) ≅ Q(cechZ)`, together with a
coaugmentation `cc : A[0] ⟶ cechZ`, *compatibly with the unit*: the compatibility clause is
the equation

`ι(rgUnit A X f) ≫ e.hom = (singleFunctorιIso).hom.app _ ≫ (singleFunctorIsoCompQ).hom.app _ ≫ Q.map cc`.

This file records that equation as a named proposition `F1UnitCompatible`, and the right-hand
side as a named morphism `unitComparison`, so that the statement of the bridge lemma

`isSplitMono_rgUnit_iff_chainSplit`

(`IsSplitMono (rgUnit A X f) ↔ ChainSplit P cc` for a K-projective `P`) can be written without
category-theoretic notation, and so that the two objects of the interface have a stable name.

`isSplitMono_rgUnit_iff_chainSplit` is the composition of the `F1` output with the criterion
`Criterion.isSplitMono_Q_map_iff_chainSplit`: it reduces the derived splitting condition of the
challenge to the chain level, hence (by `Criterion.chainSplit_iff_isUnimodular`) to the
unimodularity of `modelElem`, which is what the local-to-global algebra of this area consumes.
-/

open CategoryTheory AlgebraicGeometry

namespace Work.DSG4a

universe u

namespace Criterion

/-- The comparison morphism `A[0] → Q(P)` obtained from a coaugmentation
`cc : A[0] ⟶ P` by the canonical identifications of the single functor
(`Plus.singleFunctorιIso`, `singleFunctorIsoCompQ`).  This is the right-hand side of the
compatibility clause of the frozen area `F1`. -/
noncomputable def unitComparison (A : Type u) [CommRing A]
    [HasDerivedCategory (ModuleCat.{u} A)] (P : CochainComplex (ModuleCat.{u} A) ℤ)
    (cc : (HomologicalComplex.single (ModuleCat.{u} A) (ComplexShape.up ℤ) 0).obj
      (ModuleCat.of A A) ⟶ P) :
    DerivedCategory.Plus.ι.obj ((DerivedCategory.Plus.singleFunctor (ModuleCat.{u} A) 0).obj
      (ModuleCat.of A A)) ⟶ DerivedCategory.Q.obj P :=
  (DerivedCategory.Plus.singleFunctorιIso (ModuleCat.{u} A) 0).hom.app (ModuleCat.of A A) ≫
    (DerivedCategory.singleFunctorIsoCompQ (ModuleCat.{u} A) 0).hom.app (ModuleCat.of A A) ≫
      DerivedCategory.Q.map cc

/-- **The compatibility condition of the area `F1`.**  The image in the derived category of
the challenge unit `A[0] ⟶ RΓ(X, 𝒪)` (the map called `rgUnit` in the frozen proof map) is
the comparison morphism attached to the coaugmentation `cc` of the model `P`. -/
def F1UnitCompatible {A : Type u} [CommRing A] [HasDerivedCategory (ModuleCat.{u} A)]
    {X : Scheme.{u}} {f : X ⟶ Spec (.of A)}
    [HasDerivedCategory (SheafOfModules X.ringCatSheaf)]
    [EnoughInjectives (SheafOfModules X.ringCatSheaf)]
    (P : CochainComplex (ModuleCat.{u} A) ℤ)
    (cc : (HomologicalComplex.single (ModuleCat.{u} A) (ComplexShape.up ℤ) 0).obj
      (ModuleCat.of A A) ⟶ P)
    (e : DerivedCategory.Plus.ι.obj (DSMap.RG A X f) ≅ DerivedCategory.Q.obj P) : Prop :=
  DerivedCategory.Plus.ι.map (DSMap.rgUnit A X f) ≫ e.hom = unitComparison A P cc

end Criterion

end Work.DSG4a
