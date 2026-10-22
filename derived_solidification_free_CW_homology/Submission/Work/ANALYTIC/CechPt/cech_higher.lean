import Mathlib
import Submission.Work.ANALYTIC.CechPt.Defs
import Submission.Work.ANALYTIC.CechPt.Nerve
import Submission.Work.ANALYTIC.CechPt.cechNerve_comp_iso
import Submission.Work.ANALYTIC.CechPt.cech_acyclic_type
import Submission.Work.ANALYTIC.CechPt.afmc_whisker_iso
import Submission.Work.ANALYTIC.CechPt.isZero_map_homology

/-!
# Higher Čech homology of the Čech nerve of a map of light condensed sets vanishes

`Work.ANALYTIC.CechPt.cech_higher`: for an arbitrary morphism `β : X ⟶ Y` of light condensed sets
with `X` light profinite (no surjectivity assumed), the free-module Čech complex
`ℤ[X ×_Y ⋯ ×_Y X]` has vanishing homology in every positive degree.

The proof reduces the statement to its pointwise (set-theoretic) form:

* the *presheaf-level* Čech complex `cechPresheaf β` evaluated at a light profinite set `U` is the
  free-module Čech complex of the map of *sets* `X(U) → Y(U)`, and the alternating-face complex of
  the free module on the Čech nerve of a map of sets is acyclic above degree `0`
  (`cech_acyclic_type`); this is the only mathematical input, and it holds because the Čech nerve
  of `f : A → B` is the Čech nerve of the surjection `A → Set.range f`, whose Čech nerve splits;
* the functor `evUC U` (evaluation at `U`) commutes with the Čech nerve construction
  (`cechNerve_comp_iso`) and with homology of complexes (it is exact, `homologyMapIso`), giving the
  vanishing of the pointwise homology of the presheaf-level complex;
* sheafification is exact, so it commutes with homology (`isZero_map_homology`,
  `afmc_whisker_iso`), whence the vanishing of the homology of the light condensed Čech complex.
-/

namespace Work.ANALYTIC.CechPt

open CategoryTheory Limits LightProfinite LightCondensed AlgebraicTopology

noncomputable section

/-- Evaluation of a light condensed set at a light profinite set, written as a composite of
functors; this shape makes the limit-preservation instances available. -/
abbrev evUC (U : LightProfinite.{0}ᵒᵖ) : LightCondSet.{0} ⥤ Type 0 :=
  sheafToPresheaf cechTop (Type 0) ⋙ (CategoryTheory.evaluation LightProfinite.{0}ᵒᵖ (Type 0)).obj U

/-- `evUC U` is `evU U` (definitionally). -/
theorem evUC_eq_evU (U : LightProfinite.{0}ᵒᵖ) : evUC U = evU U := rfl

instance evUC_preserves (U : LightProfinite.{0}ᵒᵖ) (n : ℕ) :
    PreservesLimitsOfShape (WidePullbackShape (Fin (n + 1))) (evUC U) :=
  inferInstance

/-- Sheafification of `ℤ`-module presheaves on the coherent site is additive. -/
instance presheafToSheaf_additive :
    (CategoryTheory.presheafToSheaf cechTop (ModuleCat.{0} ℤ)).Additive :=
  (CategoryTheory.sheafificationAdjunction cechTop (ModuleCat.{0} ℤ)).left_adjoint_additive

variable {X : LightProfinite.{0}} {Y : LightCondSet.{0}} (β : LightProfinite.toCondensed X ⟶ Y)

/-- Evaluation at `U` of the map `β` is the map of sets `X(U) → Y(U)`. -/
lemma evUC_map (U : LightProfinite.{0}ᵒᵖ) : (evUC U).map β = β.hom.app U := rfl

/-- **Pointwise Čech complex.** The presheaf-level Čech complex of `β`, evaluated at `U`, is the
free module on the Čech nerve of the map of sets `X(U) → Y(U)`. -/
noncomputable def presheafPointwiseIso (U : LightProfinite.{0}ᵒᵖ) :
    (cechPresheaf β ⋙ evModU U) ≅
      (Arrow.cechNerve (Arrow.mk (β.hom.app U))) ⋙ ModuleCat.free ℤ :=
  (eqToIso (rfl : (cechPresheaf β ⋙ evModU U) =
    (cechNerve β ⋙ evUC U) ⋙ ModuleCat.free ℤ)) ≪≫
  (((Functor.whiskeringRight (SimplexCategoryᵒᵖ) (Type 0) (ModuleCat ℤ)).obj (ModuleCat.free ℤ)).mapIso
    ((cechNerve_comp_iso (evUC U) (Arrow.mk β)).some))

/-- **Vanishing of the pointwise Čech homology.** For every light profinite set `U`, the complex
of `U`-points of the presheaf-level Čech complex of `β` is acyclic above degree `0`. -/
lemma pointwise_isZero (U : LightProfinite.{0}ᵒᵖ) (n : ℕ) :
    IsZero ((AlgebraicTopology.AlternatingFaceMapComplex.obj
      (cechPresheaf β ⋙ evModU U)).homology (n + 1)) := by
  have hc : AlgebraicTopology.AlternatingFaceMapComplex.obj (cechPresheaf β ⋙ evModU U) ≅
      AlgebraicTopology.AlternatingFaceMapComplex.obj
        ((Arrow.cechNerve (Arrow.mk (β.hom.app U))) ⋙ ModuleCat.free ℤ) :=
    (AlgebraicTopology.alternatingFaceMapComplex (ModuleCat ℤ)).mapIso (presheafPointwiseIso β U)
  exact IsZero.of_iso (cech_acyclic_type (β.hom.app U) n)
    (HomologicalComplex.homologyMapIso hc (n + 1))

/-- **Vanishing of the presheaf-level Čech homology.** The homology presheaf of the presheaf-level
Čech complex of `β` vanishes in every positive degree. -/
lemma presheaf_isZero (n : ℕ) :
    IsZero ((AlgebraicTopology.AlternatingFaceMapComplex.obj (cechPresheaf β)).homology
      (n + 1)) := by
  rw [Functor.isZero_iff]
  intro U
  -- `evModU U` is exact, so it commutes with homology of complexes: the value at `U` of the
  -- homology presheaf is the homology of the complex of values.
  have e1 : Nonempty ((evModU U).obj
      ((AlgebraicTopology.AlternatingFaceMapComplex.obj (cechPresheaf β)).homology (n + 1)) ≅
      (((evModU U).mapHomologicalComplex (ComplexShape.down ℕ)).obj
        (AlgebraicTopology.AlternatingFaceMapComplex.obj (cechPresheaf β))).homology
        (n + 1)) :=
    ⟨(ShortComplex.mapHomologyIso
      ((AlgebraicTopology.AlternatingFaceMapComplex.obj (cechPresheaf β)).sc (n + 1))
      (evModU U)).symm⟩
  have e2 : Nonempty ((AlgebraicTopology.AlternatingFaceMapComplex.obj
        (cechPresheaf β ⋙ evModU U)).homology (n + 1) ≅
      (((evModU U).mapHomologicalComplex (ComplexShape.down ℕ)).obj
        (AlgebraicTopology.AlternatingFaceMapComplex.obj (cechPresheaf β))).homology
        (n + 1)) :=
    ⟨HomologicalComplex.homologyMapIso
      (afmc_whisker_iso (evModU U) (cechPresheaf β)).some (n + 1)⟩
  exact IsZero.of_iso (IsZero.of_iso (pointwise_isZero β U n) e2.some.symm) e1.some

theorem cech_higher {X : LightProfinite.{0}} {Y : LightCondSet.{0}}
    (β : LightProfinite.toCondensed X ⟶ Y) (n : ℕ) :
    IsZero ((AlgebraicTopology.AlternatingFaceMapComplex.obj
      (Work.ANALYTIC.CechPt.cechNerve β ⋙ free ℤ)).homology (n + 1)) := by
  rw [cechFree_eq_sheafify]
  have hh : IsZero ((((CategoryTheory.presheafToSheaf cechTop (ModuleCat.{0} ℤ)).mapHomologicalComplex
      (ComplexShape.down ℕ)).obj (AlgebraicTopology.AlternatingFaceMapComplex.obj
        (cechPresheaf β))).homology (n + 1)) :=
    isZero_map_homology _ _ (n + 1) (presheaf_isZero β n)
  exact IsZero.of_iso hh (HomologicalComplex.homologyMapIso
    (afmc_whisker_iso (CategoryTheory.presheafToSheaf cechTop (ModuleCat.{0} ℤ))
      (cechPresheaf β)).some (n + 1))

end

end Work.ANALYTIC.CechPt
