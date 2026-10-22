import Mathlib
import Submission.Work.ANALYTIC.Basic
import Submission.Work.ANALYTIC.preSolid_setup

namespace Work.ANALYTIC

open CategoryTheory Limits LightProfinite LightCondensed MonoidalCategory MonoidalClosed

noncomputable section

open _root_.LightCondensed _root_.LightCondensed.Solid

section Final

variable [PreservesFiniteLimits (tensorLeft P)]

/-- Isomorphisms of the source transport `IsIso` of the components of a natural endomorphism. -/
lemma isIso_app_of_iso {C : Type*} [Category C] {F : C ⥤ C} (γ : F ⟶ F) {X Y : C} (e : X ≅ Y)
    (hX : IsIso (γ.app X)) : IsIso (γ.app Y) := by
  have hnat := γ.naturality e.hom
  have hconj : γ.app Y = F.map e.inv ≫ γ.app X ≫ F.map e.hom := by
    calc γ.app Y = 𝟙 (F.obj Y) ≫ γ.app Y := (Category.id_comp _).symm
      _ = (F.map e.inv ≫ F.map e.hom) ≫ γ.app Y := by
            rw [← CategoryTheory.Functor.map_comp, Iso.inv_hom_id, CategoryTheory.Functor.map_id]
      _ = F.map e.inv ≫ (F.map e.hom ≫ γ.app Y) := by rw [Category.assoc]
      _ = F.map e.inv ≫ (γ.app X ≫ F.map e.hom) := by rw [hnat]
  rw [hconj]
  haveI : IsIso (γ.app X) := hX
  haveI : IsIso (F.map e.hom) := Functor.map_isIso F e.hom
  haveI : IsIso (F.map e.inv) := Functor.map_isIso F e.inv
  infer_instance

/-- `muC` is an isomorphism at a complex all of whose entries are solid. -/
lemma isIso_muC_of_solid (M : CochainComplex LightCondAb ℤ) (hM : ∀ i, isSolid (M.X i)) :
    IsIso (muC.app M) := by
  haveI : ∀ i, IsIso ((muC.app M).f i) := fun i => hM i
  exact HomologicalComplex.Hom.isIso_of_components (muC.app M)

/-- `muD` is an isomorphism at `Q.obj M` for `M` a complex of solid objects. -/
lemma isIso_muD_app_Q (M : CochainComplex LightCondAb ℤ) (hM : ∀ i, isSolid (M.X i)) :
    IsIso (muD.app (DerivedCategory.Q.obj M)) := by
  rw [muD_app_Q M]
  haveI : IsIso (muC.app M) := isIso_muC_of_solid M hM
  haveI : IsIso (DerivedCategory.Q.map (muC.app M)) := Functor.map_isIso _ _
  haveI : IsIso (fR.hom.app M) := Iso.isIso_hom (fR.app M)
  haveI : IsIso (fR.inv.app M) := Iso.isIso_inv (fR.app M)
  infer_instance

/-- `muD` is an isomorphism at the derived inclusion of every complex of solid objects. -/
lemma isIso_muD_app_derivedInclusion (N : DSolid) :
    IsIso (muD.app (derivedInclusion.obj N)) := by
  haveI hQ : (DerivedCategory.Q (C := Solid)).EssSurj :=
    Localization.essSurj (L := DerivedCategory.Q (C := Solid))
      (HomologicalComplex.quasiIso Solid (ComplexShape.up ℤ))
  obtain ⟨K, ⟨e⟩⟩ := Functor.EssSurj.mem_essImage (DerivedCategory.Q (C := Solid)) N
  -- `Q.obj (ιC.obj K) ≅ derivedInclusion.obj (Q.obj K)` and `IsIso` at the former.
  have hι : IsIso (muD.app (DerivedCategory.Q.obj (Submission.Blueprint.ιC.obj K))) :=
    isIso_muD_app_Q _ (fun i => (K.X i).property)
  have h1 : IsIso (muD.app (derivedInclusion.obj (DerivedCategory.Q.obj K))) :=
    isIso_app_of_iso muD (isSolid.ι.mapDerivedCategoryFactors.app K).symm hι
  exact isIso_app_of_iso muD (derivedInclusion.mapIso e) h1

end Final

/-- **The F7 input of REFS/01 (F6–F7) for single objects.**  Precomposition with `(1-S) ⊗ id_X` is a bijection on `Hom_D(P ⊗ X, ι N)` for every complex `N` of solid objects; this is `PreSolid X` from `Submission/Work/ANALYTIC/Basic.lean`.

Intended route: `(pre oneMinusShift).app M` is an isomorphism for solid `M` (this is the definition of `isSolid`), so applying it degreewise to the complex `ihom P (ιC N)` gives an isomorphism; transferring it across the derived adjunction `(tensorLeft P).mapDerivedCategory ⊣ (ihom P).mapDerivedCategory` (built with `Functor.mapDerivedCategory`, `NatTrans.mapDerivedCategory`, `Functor.mapDerivedCategoryCompIso`, `Functor.mapDerivedCategoryIdIso` and `Functor.mapDerivedCategorySingleFunctor`) gives the claim, since `P ⊗ X = (tensorLeft P).obj X`.  The `PreservesFiniteLimits (tensorLeft P)` input can be obtained from `Submission.Blueprint.FlatProp` via `Work.ANALYTIC.flat_P` (`import Submission.Work.ANALYTIC.flat_p`). -/
theorem preSolid_all (X : LightCondAb)
    [PreservesFiniteLimits (tensorLeft _root_.LightCondensed.P)] : PreSolid X := by
  change ∀ N : DSolid, Function.Bijective
    (fun g : (DerivedCategory.singleFunctor LightCondAb 0).obj (P ⊗ X) ⟶ derivedInclusion.obj N =>
      (DerivedCategory.singleFunctor LightCondAb 0).map (tensorOneMinusShift X) ≫ g)
  intro N
  have hpre : Function.Bijective
      (fun ψ : LD.obj ((DerivedCategory.singleFunctor LightCondAb 0).obj X) ⟶
        derivedInclusion.obj N =>
        tauD.app ((DerivedCategory.singleFunctor LightCondAb 0).obj X) ≫ ψ) := by
    haveI : IsIso (muD.app (derivedInclusion.obj N)) := isIso_muD_app_derivedInclusion N
    have hsq : (fun ψ : LD.obj ((DerivedCategory.singleFunctor LightCondAb 0).obj X) ⟶
          derivedInclusion.obj N =>
          tauD.app ((DerivedCategory.singleFunctor LightCondAb 0).obj X) ≫ ψ) =
        ⇑(adjD.homEquiv ((DerivedCategory.singleFunctor LightCondAb 0).obj X)
            (derivedInclusion.obj N)).symm ∘
          ((fun k : (DerivedCategory.singleFunctor LightCondAb 0).obj X ⟶
              RD.obj (derivedInclusion.obj N) => k ≫ muD.app (derivedInclusion.obj N)) ∘
            ⇑(adjD.homEquiv ((DerivedCategory.singleFunctor LightCondAb 0).obj X)
              (derivedInclusion.obj N))) := by
      funext ψ
      simp only [Function.comp_apply]
      symm
      rw [Equiv.symm_apply_eq]
      exact (homEquiv_tauD ((DerivedCategory.singleFunctor LightCondAb 0).obj X)
        (derivedInclusion.obj N) ψ).symm
    rw [hsq]
    exact Function.Bijective.comp (Equiv.bijective _)
      (Function.Bijective.comp
        (bijective_postcomp_iso (muD.app (derivedInclusion.obj N)) _) (Equiv.bijective _))
  have hs : tauD.app ((DerivedCategory.singleFunctor LightCondAb 0).obj X) =
      ((tensorLeft P).mapDerivedCategorySingleFunctor 0).hom.app X ≫
        (DerivedCategory.singleFunctor LightCondAb 0).map (tauP.app X) ≫
          ((tensorLeft P).mapDerivedCategorySingleFunctor 0).inv.app X :=
    NatTrans.mapDerivedCategory_app_singleFunctor_obj tauP X 0
  rw [hs] at hpre
  exact (bijective_precomp_conj_iff (((tensorLeft P).mapDerivedCategorySingleFunctor 0).app X)
    ((DerivedCategory.singleFunctor LightCondAb 0).map (tauP.app X))).mpr hpre


end

end Work.ANALYTIC
