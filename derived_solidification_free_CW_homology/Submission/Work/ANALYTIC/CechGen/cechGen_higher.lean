import Mathlib
import Submission.Work.ANALYTIC.CechPt.cech_higher
import Submission.Work.ANALYTIC.CechPt.cech_acyclic_type
import Submission.Work.ANALYTIC.CechPt.cechNerve_comp_iso

/-!
# Positive-degree acyclicity of the free Čech complex of an arbitrary map of light condensed sets

`Work.ANALYTIC.CechGen.cechGen_higher`: for an *arbitrary* morphism `β : X ⟶ Y` of light
condensed sets, with `X` an arbitrary light condensed set, the free-module Čech complex
`p ↦ ℤ[X ×_Y ⋯ ×_Y X]` is acyclic in every positive degree.

The proof is verbatim that of `Work.ANALYTIC.CechPt.cech_higher`, with the light-profinite
hypothesis on the source dropped.  Nothing in that argument ever used it:

* the *presheaf-level* Čech complex `cechGenPresheaf β` is the simplicial object
  `p ↦ ℤ[(Arrow.cechNerve β).obj p]` built inside presheaves of `ℤ`-modules, before
  sheafification, and the free-module complex `cechNerve β ⋙ free ℤ` is *by definition* its
  sheafification (`cechGenFree_eq_sheafify`);
* for a light profinite test object `U`, evaluation at `U` (which is exact) carries it to the
  free-module Čech complex of the map of *sets* `β(U) : X(U) → Y(U)`
  (`genPresheafPointwiseIso`), whose alternating-face complex is acyclic above degree `0` by the
  extra-quasi-degeneracy of any map of sets (`Work.ANALYTIC.CechPt.cech_acyclic_type`);
* hence the homology presheaf of the presheaf-level complex vanishes in positive degrees, and
  sheafification is exact, which transports this to the light condensed complex.

All the auxiliary results used (`Work.ANALYTIC.CechPt.cechNerve_comp_iso`,
`Work.ANALYTIC.CechPt.cech_acyclic_type`, `Work.ANALYTIC.CechPt.afmc_whisker_iso`,
`Work.ANALYTIC.CechPt.isZero_map_homology`) are stated for arbitrary categories, and the
functor `evUC U` (evaluation of light condensed sets at `U`) is defined on all light condensed
sets; only the *statements* in `CechPt` carry the profiniteness hypothesis, so the four
intermediate lemmas are reproved here in the general form.
-/

namespace Work.ANALYTIC.CechGen

open CategoryTheory Limits LightProfinite LightCondensed MonoidalCategory MonoidalClosed

open _root_.LightCondensed _root_.LightCondensed.Solid
open Work.ANALYTIC.CechPt

noncomputable section

/-- The *presheaf-level* Čech complex of an arbitrary morphism `β : X ⟶ Y` of light condensed
sets: the simplicial object `p ↦ ℤ[(Arrow.cechNerve β).obj p]` of presheaves of `ℤ`-modules on
light profinite sets, before sheafification.  Its sheafification is the free-module Čech complex
of `β` (`cechGenFree_eq_sheafify`). -/
abbrev cechGenPresheaf {X Y : LightCondSet.{0}} (β : X ⟶ Y) :
    SimplicialObject (LightProfinite.{0}ᵒᵖ ⥤ ModuleCat.{0} ℤ) :=
  (Arrow.cechNerve (Arrow.mk β) ⋙ sheafToPresheaf cechTop (Type 0)) ⋙
    (Functor.whiskeringRight _ _ _).obj (ModuleCat.free ℤ)

/-- The free-module Čech complex of `β` *is* the sheafification of the presheaf-level one. -/
theorem cechGenFree_eq_sheafify {X Y : LightCondSet.{0}} (β : X ⟶ Y) :
    (Arrow.cechNerve (Arrow.mk β) ⋙ free ℤ) =
      cechGenPresheaf β ⋙ presheafToSheaf cechTop (ModuleCat.{0} ℤ) := rfl

variable {X Y : LightCondSet.{0}} (β : X ⟶ Y)

/-- Evaluation at a light profinite set of the morphism `β` is the map of sets `X(U) → Y(U)`. -/
lemma evUC_map_gen (U : LightProfinite.{0}ᵒᵖ) : (evUC U).map β = β.hom.app U := rfl

/-- **Pointwise comparison.** Evaluation at `U` of the presheaf-level Čech complex of `β` is the
free-module Čech complex of the map of sets `X(U) → Y(U)`. -/
noncomputable def genPresheafPointwiseIso (U : LightProfinite.{0}ᵒᵖ) :
    (cechGenPresheaf β ⋙ evModU U) ≅
      (Arrow.cechNerve (Arrow.mk (β.hom.app U))) ⋙ ModuleCat.free ℤ :=
  (eqToIso (rfl : (cechGenPresheaf β ⋙ evModU U) =
    (Arrow.cechNerve (Arrow.mk β) ⋙ evUC U) ⋙ ModuleCat.free ℤ)) ≪≫
  (((Functor.whiskeringRight (SimplexCategoryᵒᵖ) (Type 0) (ModuleCat ℤ)).obj
      (ModuleCat.free ℤ)).mapIso
    ((cechNerve_comp_iso (evUC U) (Arrow.mk β)).some))

/-- **Vanishing of the pointwise Čech homology.** For every light profinite set `U`, the complex
of `U`-points of the presheaf-level Čech complex of `β` is acyclic above degree `0`. -/
lemma genPointwise_isZero (U : LightProfinite.{0}ᵒᵖ) (n : ℕ) :
    IsZero ((AlgebraicTopology.AlternatingFaceMapComplex.obj
      (cechGenPresheaf β ⋙ evModU U)).homology (n + 1)) := by
  have hc : AlgebraicTopology.AlternatingFaceMapComplex.obj (cechGenPresheaf β ⋙ evModU U) ≅
      AlgebraicTopology.AlternatingFaceMapComplex.obj
        ((Arrow.cechNerve (Arrow.mk (β.hom.app U))) ⋙ ModuleCat.free ℤ) :=
    (AlgebraicTopology.alternatingFaceMapComplex (ModuleCat ℤ)).mapIso
      (genPresheafPointwiseIso β U)
  exact IsZero.of_iso (cech_acyclic_type (β.hom.app U) n)
    (HomologicalComplex.homologyMapIso hc (n + 1))

/-- **Vanishing of the presheaf-level Čech homology.** The homology presheaf of the
presheaf-level Čech complex of `β` vanishes in every positive degree. -/
lemma genPresheaf_isZero (n : ℕ) :
    IsZero ((AlgebraicTopology.AlternatingFaceMapComplex.obj (cechGenPresheaf β)).homology
      (n + 1)) := by
  rw [Functor.isZero_iff]
  intro U
  -- `evModU U` is exact, so it commutes with homology of complexes: the value at `U` of the
  -- homology presheaf is the homology of the complex of values.
  have e1 : Nonempty ((evModU U).obj
      ((AlgebraicTopology.AlternatingFaceMapComplex.obj (cechGenPresheaf β)).homology (n + 1)) ≅
      (((evModU U).mapHomologicalComplex (ComplexShape.down ℕ)).obj
        (AlgebraicTopology.AlternatingFaceMapComplex.obj (cechGenPresheaf β))).homology
        (n + 1)) :=
    ⟨(ShortComplex.mapHomologyIso
      ((AlgebraicTopology.AlternatingFaceMapComplex.obj (cechGenPresheaf β)).sc (n + 1))
      (evModU U)).symm⟩
  have e2 : Nonempty ((AlgebraicTopology.AlternatingFaceMapComplex.obj
        (cechGenPresheaf β ⋙ evModU U)).homology (n + 1) ≅
      (((evModU U).mapHomologicalComplex (ComplexShape.down ℕ)).obj
        (AlgebraicTopology.AlternatingFaceMapComplex.obj (cechGenPresheaf β))).homology
        (n + 1)) :=
    ⟨HomologicalComplex.homologyMapIso
      (afmc_whisker_iso (evModU U) (cechGenPresheaf β)).some (n + 1)⟩
  exact IsZero.of_iso (IsZero.of_iso (genPointwise_isZero β U n) e2.some.symm) e1.some

/-- **Positive-degree acyclicity of the free Čech complex, arbitrary source.**
For an *arbitrary* morphism `β : X ⟶ Y` of light condensed sets (no surjectivity assumed), where
`X` is an arbitrary light condensed set, the free-module Čech complex `p ↦ ℤ[X ×_Y ⋯ ×_Y X]` has
vanishing homology in every positive degree.

The identical statement with `X` *light profinite* is proved in
`Submission/Work/ANALYTIC/CechPt/cech_higher.lean` (`Work.ANALYTIC.CechPt.cech_higher`); that
proof is *pointwise*: at a light profinite test object `U` the level-`p` term is the free module
on the Čech nerve of the map of *sets* `X(U) → Y(U)`, which has an extra degeneracy
(`CechPt/cech_acyclic_type.lean`), and evaluation at `U` as well as sheafification are exact. No
step uses that `X` is light profinite. -/
theorem cechGen_higher {X Y : LightCondSet.{0}} (β : X ⟶ Y) (n : ℕ) :
    IsZero ((AlgebraicTopology.AlternatingFaceMapComplex.obj
      (Arrow.cechNerve (Arrow.mk β) ⋙ free ℤ)).homology (n + 1)) := by
  rw [cechGenFree_eq_sheafify]
  have hh : IsZero ((((CategoryTheory.presheafToSheaf cechTop
      (ModuleCat.{0} ℤ)).mapHomologicalComplex
      (ComplexShape.down ℕ)).obj (AlgebraicTopology.AlternatingFaceMapComplex.obj
        (cechGenPresheaf β))).homology (n + 1)) :=
    isZero_map_homology _ _ (n + 1) (genPresheaf_isZero β n)
  exact IsZero.of_iso hh (HomologicalComplex.homologyMapIso
    (afmc_whisker_iso (CategoryTheory.presheafToSheaf cechTop (ModuleCat.{0} ℤ))
      (cechGenPresheaf β)).some (n + 1))

end

end Work.ANALYTIC.CechGen
