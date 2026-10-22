import Mathlib
import Submission.Work.ANALYTIC.CechPt.Setup
import Submission.Work.ANALYTIC.CechPt.Nerve

/-!
# The Čech complex of a cover: definitions

This module collects the definitions used by `Submission.Work.ANALYTIC.CechPt.cech_descent`:

* `cechTop` — the coherent topology on light profinite sets;
* `evU` — evaluation of a light condensed set at a light profinite set, i.e. the functor
  `F ↦ F(U) = Hom(U, F)`;
* `cechPresheaf` — the *presheaf-level* Čech complex of a map `β : X ⟶ Y`, i.e. the complex of
  presheaves `p ↦ ℤ[(Arrow.cechNerve β).obj p]` built inside presheaves of abelian groups, before
  sheafification;
* `corestrU` — the map induced by `β` on `U`-points, corestricted to its range;
* `typeCech_quasiIso_of_splitEpi` — Mathlib's extra-degeneracy argument in the split case.

The point of the presheaf-level complex is that its sheafification *is* the complex of free light
condensed abelian groups (see `cechFree_eq_sheafify`), while it can be evaluated pointwise.
-/

namespace Work.ANALYTIC.CechPt

open CategoryTheory Limits LightProfinite LightCondensed AlgebraicTopology

noncomputable section

/-- The coherent topology on light profinite sets. -/
abbrev cechTop : GrothendieckTopology LightProfinite.{0} := coherentTopology LightProfinite.{0}

/-- Evaluation of a light condensed set at a light profinite set. -/
abbrev evU (U : LightProfinite.{0}ᵒᵖ) : LightCondSet.{0} ⥤ Type 0 where
  obj F := F.obj.obj U
  map f := f.hom.app U

/-- Evaluation of a presheaf of `ℤ`-modules on light profinite sets at a light profinite set. -/
abbrev evModU (U : LightProfinite.{0}ᵒᵖ) :
    (LightProfinite.{0}ᵒᵖ ⥤ ModuleCat.{0} ℤ) ⥤ ModuleCat.{0} ℤ :=
  (CategoryTheory.evaluation LightProfinite.{0}ᵒᵖ (ModuleCat.{0} ℤ)).obj U

/-- The *presheaf-level* Čech complex of `β : X ⟶ Y`: the presheaf of free abelian groups on the
points of the Čech nerve.  Its sheafification (for the coherent topology) is the simplicial object
`p ↦ ℤ[(Arrow.cechNerve β).obj p]` of light condensed abelian groups. -/
abbrev cechPresheaf {X : LightProfinite.{0}} {Y : LightCondSet.{0}}
    (β : LightProfinite.toCondensed X ⟶ Y) :
    SimplicialObject (LightProfinite.{0}ᵒᵖ ⥤ ModuleCat.{0} ℤ) :=
  (cechNerve β ⋙ sheafToPresheaf cechTop (Type 0)) ⋙
    (Functor.whiskeringRight _ _ _).obj (ModuleCat.free ℤ)

/-- The free-module Čech complex of `β` *is* the sheafification of the presheaf-level one. -/
theorem cechFree_eq_sheafify {X : LightProfinite.{0}} {Y : LightCondSet.{0}}
    (β : LightProfinite.toCondensed X ⟶ Y) :
    (cechNerve β ⋙ free ℤ) = cechPresheaf β ⋙ presheafToSheaf cechTop (ModuleCat.{0} ℤ) :=
  rfl

/-- The map induced by `β` on `U`-points, corestricted to its range. -/
abbrev corestrU {X : LightProfinite.{0}} {Y : LightCondSet.{0}}
    (β : LightProfinite.toCondensed X ⟶ Y) (U : LightProfinite.{0}ᵒᵖ) :
    ((LightProfinite.toCondensed X).obj.obj U) ⟶
      ↥(Set.range fun a => β.hom.app U a) :=
  ↾(fun a => (⟨β.hom.app U a, ⟨a, rfl⟩⟩ : Set.range fun a => β.hom.app U a))

/-- The corestriction of `β` at `U` is surjective. -/
theorem corestrU_surjective {X : LightProfinite.{0}} {Y : LightCondSet.{0}}
    (β : LightProfinite.toCondensed X ⟶ Y) (U : LightProfinite.{0}ᵒᵖ) :
    Function.Surjective fun a => (corestrU β U) a := by
  intro b
  obtain ⟨a, ha⟩ := b.2
  exact ⟨a, Subtype.ext ha⟩

/-- **Type-level, split case.**  For a split epimorphism `f : A ⟶ B` of types, the augmentation
of the free-module Čech complex of the Čech nerve of `f` is a quasi-isomorphism onto `ℤ[B]`.
This is the `SplitEpi` case of Mathlib's `Arrow.AugmentedCechNerve.extraDegeneracy` combined with
`SimplicialObject.Augmented.ExtraDegeneracy.homotopyEquiv`. -/
theorem typeCech_quasiIso_of_splitEpi {A B : Type} (f : A ⟶ B) (S : SplitEpi f) :
    QuasiIso (AlgebraicTopology.AlternatingFaceMapComplex.ε.app
      ((SimplicialObject.Augmented.whiskeringObj Type (ModuleCat.{0} ℤ) (ModuleCat.free ℤ)).obj
        (Arrow.augmentedCechNerve (Arrow.mk f)))) :=
  (SimplicialObject.Augmented.ExtraDegeneracy.homotopyEquiv
    ((Arrow.AugmentedCechNerve.extraDegeneracy (Arrow.mk f) S).map (ModuleCat.free ℤ))).quasiIso_hom

end

end Work.ANALYTIC.CechPt
