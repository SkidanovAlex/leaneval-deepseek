import Mathlib
import Submission.Work.ANALYTIC.CechPt.cech_higher
import Submission.Work.ANALYTIC.CechPt.cech_acyclic_type
import Submission.Work.ANALYTIC.CechPt.afmc_whisker_iso
import Submission.Work.ANALYTIC.CechPt.isZero_map_homology
import Submission.Work.ANALYTIC.CechLight.cech_descent_light_homologyMap_zero

namespace Work.ANALYTIC

open CategoryTheory Limits LightProfinite LightCondensed MonoidalCategory MonoidalClosed
open _root_.LightCondensed _root_.LightCondensed.Solid

noncomputable section

/-!
# Čech descent for an arbitrary light condensed source

The goal of this file is `Work.ANALYTIC.cech_descent_light`: for an epimorphism `β : X ⟶ Y` of
light condensed sets with `X` an *arbitrary* light condensed set, the augmented Čech complex of
`ℤ[-]` applied to the Čech nerve of `β` is a resolution of `ℤ[Y]` (a quasi-isomorphism onto `ℤ[Y]`
concentrated in degree `0`).

The proof runs the standard "presheaf-level plus exactness of sheafification" argument, which does
*not* need `X` to be light profinite:

* `preCechS β` is the **presheaf-level** Čech complex of `β`: the presheaf of free `ℤ`-modules on
  the points of the Čech nerve.  Its sheafification is the light condensed Čech complex
  (`preCechS_eq_sheafify`, by `rfl`).
* Pointwise, at any light profinite set `U`, evaluation at `U` turns this into the Čech complex of
  the *map of sets* `X(U) ⟶ Y(U)`: this is `CechPt.cechNerve_comp_iso` ("the Čech nerve commutes
  with functors preserving the relevant wide pullbacks") applied to the evaluation functor,
  combined with the definitional description of the differentials.
* The alternating face map complex of the free `ℤ`-modules on the Čech nerve of *any* map of sets
  is acyclic in positive degrees (`CechPt.cech_acyclic_type`), so the pointwise homology of the
  presheaf-level complex vanishes, and hence — homology of a complex of presheaves is pointwise —
  the homology presheaf itself vanishes (`preCechS_isZero`).
* Sheafification (`presheafToSheaf`) is exact, so it commutes with homology of complexes
  (`CechPt.isZero_map_homology`), and the vanishing descends to the light condensed Čech complex
  (`cechNerve_higher_isZero`), which is `AFMC.obj (cechNerve β ⋙ free ℤ)` up to the canonical
  identification `CechPt.afmc_whisker_iso`.

Degree `0` — the statement that the augmentation exhibits `ℤ[Y]` as the coequalizer of the two
face maps, using that epimorphisms of light condensed sets are effective — is
`Work.ANALYTIC.CechLight.cech_descent_light_homologyMap_zero`; the final assembly uses
`quasiIso_iff` and `quasiIsoAt_iff_isIso_homologyMap`.
-/

/-- The **presheaf-level Čech nerve of `β`**: the underlying presheaves of the Čech nerve of `β`,
with `ℤ[-]` applied (an arbitrary source `X`). -/
abbrev preCechS {X Y : LightCondSet.{0}} (β : X ⟶ Y) :
    SimplicialObject (LightProfinite.{0}ᵒᵖ ⥤ ModuleCat.{0} ℤ) :=
  ((Arrow.cechNerve (Arrow.mk β)) ⋙
      sheafToPresheaf (coherentTopology LightProfinite.{0}) (Type 0)) ⋙
    (Functor.whiskeringRight _ _ _).obj (ModuleCat.free ℤ)

/-- The light condensed Čech complex of `β` is the levelwise sheafification of the
presheaf-level one. -/
theorem preCechS_eq_sheafify {X Y : LightCondSet.{0}} (β : X ⟶ Y) :
    (Arrow.cechNerve (Arrow.mk β) ⋙ free ℤ) =
      preCechS β ⋙ presheafToSheaf (coherentTopology LightProfinite.{0}) (ModuleCat.{0} ℤ) :=
  rfl

/-- **Pointwise description of the presheaf-level Čech complex.**  Evaluating `preCechS β` at a
light profinite set `U` gives the free-module Čech complex of the *map of sets*
`X(U) ⟶ Y(U)`.

The first factor is definitional; the second is `CechPt.cechNerve_comp_iso` for the evaluation
functor `CechPt.evUC U`, which preserves the wide pullbacks out of which the Čech nerve is
built. -/
noncomputable def preCechS_pointwise_iso {X Y : LightCondSet.{0}} (β : X ⟶ Y) (U : LightProfinite.{0}ᵒᵖ) :
    (preCechS β ⋙ (CategoryTheory.evaluation (LightProfinite.{0}ᵒᵖ) (ModuleCat.{0} ℤ)).obj U) ≅
      (Arrow.cechNerve (Arrow.mk (β.hom.app U))) ⋙ ModuleCat.free ℤ :=
  (eqToIso (rfl : (preCechS β ⋙
      (CategoryTheory.evaluation (LightProfinite.{0}ᵒᵖ) (ModuleCat.{0} ℤ)).obj U) =
    ((Arrow.cechNerve (Arrow.mk β)) ⋙ CechPt.evUC U) ⋙ ModuleCat.free ℤ)) ≪≫
  (((Functor.whiskeringRight (SimplexCategoryᵒᵖ) (Type 0) (ModuleCat ℤ)).obj
      (ModuleCat.free ℤ)).mapIso
    ((CechPt.cechNerve_comp_iso (CechPt.evUC U) (Arrow.mk β)).some))

/-- **Vanishing of the pointwise Čech homology** for an arbitrary source: at every light profinite
set `U`, the complex of `U`-points of the presheaf-level Čech complex of `β` is acyclic above
degree `0`.  This is the type-level input `CechPt.cech_acyclic_type`. -/
theorem preCechS_pointwise_isZero {X Y : LightCondSet.{0}} (β : X ⟶ Y)
    (U : LightProfinite.{0}ᵒᵖ) (n : ℕ) :
    IsZero ((AlgebraicTopology.AlternatingFaceMapComplex.obj
      (preCechS β ⋙ (CategoryTheory.evaluation (LightProfinite.{0}ᵒᵖ)
        (ModuleCat.{0} ℤ)).obj U)).homology (n + 1)) := by
  have hc : AlgebraicTopology.AlternatingFaceMapComplex.obj (preCechS β ⋙
        (CategoryTheory.evaluation (LightProfinite.{0}ᵒᵖ) (ModuleCat.{0} ℤ)).obj U) ≅
      AlgebraicTopology.AlternatingFaceMapComplex.obj
        ((Arrow.cechNerve (Arrow.mk (β.hom.app U))) ⋙ ModuleCat.free ℤ) :=
    (AlgebraicTopology.alternatingFaceMapComplex (ModuleCat ℤ)).mapIso (preCechS_pointwise_iso β U)
  exact IsZero.of_iso (CechPt.cech_acyclic_type (β.hom.app U) n)
    (HomologicalComplex.homologyMapIso hc (n + 1))

/-- **Vanishing of the presheaf-level Čech homology** for an arbitrary source: the homology
presheaf of `preCechS β` vanishes in every positive degree.  Homology of complexes of presheaves
is computed pointwise, and pointwise the complex is acyclic (`preCechS_pointwise_isZero`). -/
theorem preCechS_isZero {X Y : LightCondSet.{0}} (β : X ⟶ Y) (n : ℕ) :
    IsZero ((AlgebraicTopology.AlternatingFaceMapComplex.obj (preCechS β)).homology
      (n + 1)) := by
  rw [Functor.isZero_iff]
  intro U
  -- evaluation is exact, so it commutes with homology of complexes: the value at `U` of the
  -- homology presheaf is the homology of the complex of values.
  have e1 : Nonempty (((CategoryTheory.evaluation (LightProfinite.{0}ᵒᵖ)
        (ModuleCat.{0} ℤ)).obj U).obj
      ((AlgebraicTopology.AlternatingFaceMapComplex.obj (preCechS β)).homology (n + 1)) ≅
      (((((CategoryTheory.evaluation (LightProfinite.{0}ᵒᵖ)
        (ModuleCat.{0} ℤ)).obj U).mapHomologicalComplex (ComplexShape.down ℕ)).obj
        (AlgebraicTopology.AlternatingFaceMapComplex.obj (preCechS β))).homology
        (n + 1))) :=
    ⟨(ShortComplex.mapHomologyIso
      ((AlgebraicTopology.AlternatingFaceMapComplex.obj (preCechS β)).sc (n + 1))
      ((CategoryTheory.evaluation (LightProfinite.{0}ᵒᵖ) (ModuleCat.{0} ℤ)).obj U)).symm⟩
  have e2 : Nonempty ((AlgebraicTopology.AlternatingFaceMapComplex.obj
        (preCechS β ⋙ (CategoryTheory.evaluation (LightProfinite.{0}ᵒᵖ)
          (ModuleCat.{0} ℤ)).obj U)).homology (n + 1) ≅
      (((((CategoryTheory.evaluation (LightProfinite.{0}ᵒᵖ)
        (ModuleCat.{0} ℤ)).obj U).mapHomologicalComplex (ComplexShape.down ℕ)).obj
        (AlgebraicTopology.AlternatingFaceMapComplex.obj (preCechS β))).homology
        (n + 1))) :=
    ⟨HomologicalComplex.homologyMapIso
      ((CechPt.afmc_whisker_iso ((CategoryTheory.evaluation (LightProfinite.{0}ᵒᵖ)
        (ModuleCat.{0} ℤ)).obj U) (preCechS β)).some) (n + 1)⟩
  exact IsZero.of_iso (IsZero.of_iso (preCechS_pointwise_isZero β U n) e2.some.symm) e1.some

/-- **Čech descent in positive degrees, arbitrary source.**  For any `β : X ⟶ Y` of light
condensed sets (no assumption on `X`), the light condensed Čech complex `ℤ[X ×_Y ⋯ ×_Y X]` of
`β` has vanishing homology in every positive degree. -/
theorem cechNerve_higher_isZero {X Y : LightCondSet.{0}} (β : X ⟶ Y) (n : ℕ) :
    IsZero ((AlgebraicTopology.AlternatingFaceMapComplex.obj
      (Arrow.cechNerve (Arrow.mk β) ⋙ free ℤ)).homology (n + 1)) := by
  rw [preCechS_eq_sheafify]
  have hh : IsZero ((((CategoryTheory.presheafToSheaf (coherentTopology LightProfinite.{0})
      (ModuleCat.{0} ℤ)).mapHomologicalComplex
      (ComplexShape.down ℕ)).obj (AlgebraicTopology.AlternatingFaceMapComplex.obj
        (preCechS β))).homology (n + 1)) :=
    CechPt.isZero_map_homology _ _ (n + 1) (preCechS_isZero β n)
  exact IsZero.of_iso hh (HomologicalComplex.homologyMapIso
    ((CechPt.afmc_whisker_iso (CategoryTheory.presheafToSheaf (coherentTopology LightProfinite.{0})
      (ModuleCat.{0} ℤ)) (preCechS β)).some) (n + 1))

/-- The augmented simplicial object whose alternating-face complex is the light condensed Čech
complex of `β`. -/
abbrev augCechLight {X Y : LightCondSet.{0}} (β : X ⟶ Y) : SimplicialObject.Augmented LightCondAb :=
  (SimplicialObject.Augmented.whiskeringObj _ LightCondAb (free ℤ)).obj
    (Arrow.augmentedCechNerve (Arrow.mk β))

end

/-- **Čech descent, arbitrary source.**  For an epimorphism `β : X ⟶ Y` of light condensed sets,
where `X` is an *arbitrary* light condensed set (not necessarily light profinite), the augmented
Čech nerve of `β`, with `ℤ[-]` applied and pushed through the alternating-face-map complex, maps
quasi-isomorphically onto `ℤ[Y]` concentrated in degree `0`. -/
theorem cech_descent_light {X Y : LightCondSet.{0}} (β : X ⟶ Y) (hβ : Epi β) :
    QuasiIso (AlgebraicTopology.AlternatingFaceMapComplex.ε.app
      ((SimplicialObject.Augmented.whiskeringObj _ LightCondAb (free ℤ)).obj
        (Arrow.augmentedCechNerve (Arrow.mk β)))) := by
  rw [quasiIso_iff]
  intro i
  rw [quasiIsoAt_iff_isIso_homologyMap]
  match i with
  | 0 => exact CechLight.cech_descent_light_homologyMap_zero β hβ
  | (n + 1) =>
      refine IsZero.isIso ?_ ?_ _
      · exact cechNerve_higher_isZero β n
      · exact HomologicalComplex.isZero_single_obj_homology (ComplexShape.down ℕ) 0
          ((free ℤ).obj Y) (n + 1) (Nat.succ_ne_zero n)

end Work.ANALYTIC
