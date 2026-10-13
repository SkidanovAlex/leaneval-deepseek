import Mathlib
import Submission.Work.DSF1.Sheaf.acyclicAffineHomDefs
import Submission.Work.DSF1.Sheaf.rightDerived_iso_homology_of_acyclic_resolution
import Submission.Work.DSF1.Sheaf.rightDerived_comp_exact
import Submission.Work.DSF1.Sheaf.cechTrivAt_iff_homology
import Submission.Work.DSF1.Sheaf.pushforward_injective
import Submission.Work.DSF1.Sheaf.affineHomAcycAux
import Submission.Work.DSEQ0.AugDefs
import Submission.Work.DSEQ0.SepBasic
import Submission.Work.DSEQ0.atv_machine
import Submission.Work.DSEQ0.isZero_homology_sections_injectiveResolution
import Submission.Work.DSEQ0.restrictFunctor_preservesHomology
import Submission.Work.DSG1.enoughInjectives_sheafOfModules
import Submission.Work.DSG1.injectiveIsFlasque

/-!
# Serre vanishing for the structure sheaf on an affine open

`Work.DSF1.Sheaf.sectionsAffineAcyclic_proved`: for a scheme `Y` (here `Y = W.toScheme` for an
open `W` of a scheme `X`), an affine open `U ⊆ Y` and *any* injective resolution `I` of the
structure sheaf `𝒪_Y`, the complex of sections `Γ(U, I^•)` is acyclic in positive degrees:
`H^n (Γ(U, I^•)) = 0` for `n > 0`.

Equivalently `R^q Γ(U, -)(𝒪_Y) = H^q(U, 𝒪_Y) = 0` for `q > 0`, i.e. Serre vanishing for the
affine open `U`.

## Strategy

The affine scheme `U.toScheme` is where the Čech/Serre argument can be run, so the given
resolution is transported to `U.toScheme` along the restriction functor
`R := Scheme.Modules.restrictFunctor (Opens.ι U)` (an exact functor):

* `Γ(U, -)` is naturally isomorphic to `R ⋙ Γ(⊤, -)` (`restrictIso_sectionsFunctor` below, whose
  components come from `Scheme.Modules.restrict_obj`, an `rfl`-level identification);
* the restricted complex `K := R (I.cocomplex)` consists of flasque sheaves of modules (the
  restriction of a flasque sheaf is flasque, and the terms of `I` are injective, hence flasque by
  `Work.DSG1.injectiveIsFlasque`), while the augmentation `R(𝒪_Y)[0] ⟶ K` induced by `I.ι` is a
  quasi-isomorphism because it is the image of the quasi-isomorphism `I.ι` under the exact
  functor `R` (transported along `HomologicalComplex.singleMapHomologicalComplex`);
* flasque sheaves on the affine scheme `U.toScheme` are acyclic for global sections: Čech
  triviality (`Work.DSEQ0.flasque_hasCechCohomology'`) plus
  `Work.DSEQ0.isZero_rightDerived_of_cechTrivOnBasic`;
* the acyclic-resolution criterion
  `Work.DSF1.Sheaf.rightDerived_iso_homology_of_acyclic_resolution` therefore computes
  `R^n Γ(⊤, -)` on `K`, and
* `R^n Γ(⊤, -)(𝒪_{U.toScheme}) = 0` for `n > 0` is Serre vanishing for the affine scheme
  `U.toScheme`, available as `Work.DSEQ0.isZero_homology_sections_injectiveResolution`.

Finally `Γ(U, I^•) ≅ Γ(⊤, R(I^•))` via `restrictIso_sectionsFunctor`, which yields the claim.
-/

universe u

namespace Work.DSF1.Sheaf

open CategoryTheory AlgebraicGeometry Opposite Limits

set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

/-- Naturality of the action of a morphism of `𝒪_Y`-modules on sections, along an identification
of the opens. -/
private lemma app_eqToHom_naturality_aux {Y : AlgebraicGeometry.Scheme.{u}} {M N : Y.Modules}
    (φ : M ⟶ N) {V V' : Y.Opens} (e : V = V') :
    AlgebraicGeometry.Scheme.Modules.Hom.app φ V ≫
        N.presheaf.map (CategoryTheory.eqToHom (congrArg Opposite.op e)) =
      M.presheaf.map (CategoryTheory.eqToHom (congrArg Opposite.op e)) ≫
        AlgebraicGeometry.Scheme.Modules.Hom.app φ V' := by
  have h := (AlgebraicGeometry.Scheme.Modules.Hom.mapPresheaf φ).naturality
    (CategoryTheory.eqToHom (congrArg Opposite.op e))
  simpa using h.symm

/-- **Sections over an open, as global sections of the restriction.**  The functor `Γ(U, -)` on
`Y.Modules` is naturally isomorphic to the composite of the restriction to the open subscheme `U`
with the global sections functor on `U.toScheme`. -/
private noncomputable def restrictIso_sectionsFunctor (Y : AlgebraicGeometry.Scheme.{u})
    (U : Y.Opens) :
    CategoryTheory.Iso
      (CategoryTheory.Functor.comp
        (AlgebraicGeometry.Scheme.Modules.restrictFunctor (AlgebraicGeometry.Scheme.Opens.ι U))
        (Work.DSF1.Sheaf.sectionsFunctor U.toScheme (⊤ : U.toScheme.Opens)))
      (Work.DSF1.Sheaf.sectionsFunctor Y U) := by
  have h : (AlgebraicGeometry.Scheme.Opens.ι U) ''ᵁ (⊤ : U.toScheme.Opens) = U := by
    rw [AlgebraicGeometry.Scheme.Hom.image_top_eq_opensRange,
      AlgebraicGeometry.Scheme.Opens.opensRange_ι]
  refine CategoryTheory.NatIso.ofComponents (fun M =>
    CategoryTheory.eqToIso (AlgebraicGeometry.Scheme.Modules.restrict_obj M
      (AlgebraicGeometry.Scheme.Opens.ι U) (⊤ : U.toScheme.Opens)) ≪≫
      M.presheaf.mapIso (CategoryTheory.eqToIso (congrArg Opposite.op h))) ?_
  intro M N φ
  simp only [CategoryTheory.Functor.comp_obj, CategoryTheory.Functor.comp_map,
    Work.DSEQ0.sectionsV_map, CategoryTheory.Functor.mapIso_hom, CategoryTheory.eqToIso.hom]
  exact app_eqToHom_naturality_aux φ h

theorem sectionsAffineAcyclic_proved {X : AlgebraicGeometry.Scheme.{u}} {W : X.Opens} (U : W.toScheme.Opens) (hU : AlgebraicGeometry.IsAffineOpen U) (I : CategoryTheory.InjectiveResolution (SheafOfModules.unit W.toScheme.ringCatSheaf)) (n : ℕ) (hn : 0 < n) : CategoryTheory.Limits.IsZero ((HomologicalComplex.homologyFunctor AddCommGrpCat.{u} (ComplexShape.up ℕ) n).obj (((Work.DSF1.Sheaf.sectionsFunctor W.toScheme U).mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex)) := by
  haveI : AlgebraicGeometry.IsAffine U.toScheme := hU
  haveI : CategoryTheory.EnoughInjectives (AlgebraicGeometry.Scheme.Modules U.toScheme) :=
    Work.DSG1.enoughInjectives_sheafOfModules U.toScheme
  -- instances for the restriction functor
  haveI hRad : (AlgebraicGeometry.Scheme.Modules.restrictFunctor
      (AlgebraicGeometry.Scheme.Opens.ι U)).Additive := by
    haveI : PreservesBinaryBiproducts (AlgebraicGeometry.Scheme.Modules.restrictFunctor
        (AlgebraicGeometry.Scheme.Opens.ι U)) :=
      preservesBinaryBiproducts_of_preservesBinaryCoproducts _
    exact Functor.additive_of_preservesBinaryBiproducts _
  haveI hRhom : (AlgebraicGeometry.Scheme.Modules.restrictFunctor
      (AlgebraicGeometry.Scheme.Opens.ι U)).PreservesHomology :=
    Work.DSEQ0.restrictFunctor_preservesHomology (AlgebraicGeometry.Scheme.Opens.ι U)
  -- instances for the sections functor
  haveI hAdd : (Work.DSEQ0.sectionsV U.toScheme (⊤ : U.toScheme.Opens)).Additive :=
    Work.DSEQ0.sectionsV_additive U.toScheme ⊤
  haveI hFL : PreservesFiniteLimits (Work.DSEQ0.sectionsV U.toScheme (⊤ : U.toScheme.Opens)) :=
    Limits.comp_preservesFiniteLimits
      (SheafOfModules.evaluation U.toScheme.ringCatSheaf (Opposite.op (⊤ : U.toScheme.Opens)))
      (CategoryTheory.forget₂
        (ModuleCat.{u} (U.toScheme.ringCatSheaf.obj.obj (Opposite.op (⊤ : U.toScheme.Opens))))
        AddCommGrpCat.{u})
  -- the restriction of the given injective resolution
  let K : CochainComplex U.toScheme.Modules ℕ :=
    ((AlgebraicGeometry.Scheme.Modules.restrictFunctor (AlgebraicGeometry.Scheme.Opens.ι U)
      ).mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex
  -- the induced augmentation, a quasi-isomorphism because `I.ι` is one and `R` is exact
  let q' : (CochainComplex.single₀ U.toScheme.Modules).obj
      ((AlgebraicGeometry.Scheme.Modules.restrictFunctor (AlgebraicGeometry.Scheme.Opens.ι U)).obj
        (SheafOfModules.unit W.toScheme.ringCatSheaf)) ⟶ K :=
    (HomologicalComplex.singleMapHomologicalComplex
        (AlgebraicGeometry.Scheme.Modules.restrictFunctor (AlgebraicGeometry.Scheme.Opens.ι U))
        (ComplexShape.up ℕ) 0).inv.app (SheafOfModules.unit W.toScheme.ringCatSheaf) ≫
      ((AlgebraicGeometry.Scheme.Modules.restrictFunctor (AlgebraicGeometry.Scheme.Opens.ι U)
        ).mapHomologicalComplex (ComplexShape.up ℕ)).map I.ι
  haveI hQ : QuasiIso q' := inferInstance
  -- the terms of `K` are flasque: restrictions of injective, hence flasque, sheaves
  have hfl : ∀ m : ℕ, TopCat.Presheaf.IsFlasque
      ((SheafOfModules.toSheaf U.toScheme.ringCatSheaf).obj (K.X m)).obj := by
    intro m
    haveI : CategoryTheory.Injective (I.cocomplex.X m) := I.injective m
    have hflI := Work.DSG1.injectiveIsFlasque W.toScheme (I.cocomplex.X m)
    refine ⟨fun {A B} i => ?_⟩
    exact hflI.epi ((Scheme.Hom.opensFunctor (Scheme.Opens.ι U)).op.map i)
  -- flasque sheaves on the affine scheme `U.toScheme` are acyclic for global sections
  have hac : ∀ (m k : ℕ), 0 < k → IsZero
      (((Work.DSEQ0.sectionsV U.toScheme (⊤ : U.toScheme.Opens)).rightDerived k).obj (K.X m)) := by
    intro m k hk
    have hZ : Work.DSEQ0.CechTrivOnBasic U.toScheme (K.X m) := by
      intro ι _ f g hmem hcov t ht
      obtain ⟨j, rfl⟩ : ∃ j, t = j + 1 := ⟨t - 1, by omega⟩
      exact (Work.DSF1.Sheaf.cechTrivAt_iff_homology _ j).mp
        ((Work.DSEQ0.flasque_hasCechCohomology' (K.X m) (hfl m))
          (fun i => U.toScheme.basicOpen (f i)) j)
    have h1 : IsZero
        (((SheafOfModules.evaluation U.toScheme.ringCatSheaf
          (Opposite.op (⊤ : U.toScheme.Opens))).rightDerived k).obj (K.X m)) :=
      Work.DSEQ0.isZero_rightDerived_of_cechTrivOnBasic U.toScheme (K.X m) hZ k hk
    obtain ⟨e3⟩ := Work.DSF1.Sheaf.rightDerived_comp_exact
      (SheafOfModules.evaluation U.toScheme.ringCatSheaf (Opposite.op (⊤ : U.toScheme.Opens)))
      (CategoryTheory.forget₂
        (ModuleCat.{u} (U.toScheme.ringCatSheaf.obj.obj (Opposite.op (⊤ : U.toScheme.Opens))))
        AddCommGrpCat.{u}) (K.X m) k
    have h2 := Functor.map_isZero
      (CategoryTheory.forget₂
        (ModuleCat.{u} (U.toScheme.ringCatSheaf.obj.obj (Opposite.op (⊤ : U.toScheme.Opens))))
        AddCommGrpCat.{u}) h1
    refine IsZero.of_iso h2 ?_
    exact e3
  -- Serre vanishing for the structure sheaf of the affine scheme `U.toScheme`
  let J : CategoryTheory.InjectiveResolution (SheafOfModules.unit U.toScheme.ringCatSheaf) :=
    CategoryTheory.injectiveResolution _
  have hK0 : IsZero (((Work.DSEQ0.sectionsV U.toScheme (⊤ : U.toScheme.Opens)).rightDerived n).obj
      (SheafOfModules.unit U.toScheme.ringCatSheaf)) :=
    IsZero.of_iso
      (Work.DSEQ0.isZero_homology_sections_injectiveResolution U.toScheme J n hn)
      (J.isoRightDerivedObj (Work.DSEQ0.sectionsV U.toScheme (⊤ : U.toScheme.Opens)) n)
  -- the acyclic-resolution criterion computes `R^n Γ(⊤, -)` on the restricted resolution
  have hK1 : IsZero ((HomologicalComplex.homologyFunctor AddCommGrpCat.{u} (ComplexShape.up ℕ) n).obj
      (((Work.DSEQ0.sectionsV U.toScheme (⊤ : U.toScheme.Opens)).mapHomologicalComplex
        (ComplexShape.up ℕ)).obj K)) := by
    obtain ⟨e4⟩ := Work.DSF1.Sheaf.rightDerived_iso_homology_of_acyclic_resolution
      (Work.DSEQ0.sectionsV U.toScheme (⊤ : U.toScheme.Opens))
      ((AlgebraicGeometry.Scheme.Modules.restrictFunctor (AlgebraicGeometry.Scheme.Opens.ι U)).obj
        (SheafOfModules.unit W.toScheme.ringCatSheaf)) K q' hac n
    have h2 : IsZero (((Work.DSEQ0.sectionsV U.toScheme (⊤ : U.toScheme.Opens)).rightDerived n).obj
        ((AlgebraicGeometry.Scheme.Modules.restrictFunctor (AlgebraicGeometry.Scheme.Opens.ι U)).obj
          (SheafOfModules.unit W.toScheme.ringCatSheaf))) :=
      IsZero.of_iso hK0 (((Work.DSEQ0.sectionsV U.toScheme (⊤ : U.toScheme.Opens)).rightDerived n).mapIso
        (AlgebraicGeometry.Scheme.Modules.restrictUnitIso (AlgebraicGeometry.Scheme.Opens.ι U)))
    exact IsZero.of_iso h2 e4.symm
  -- comparison of `Γ(U, -)` with `Γ(⊤, -) ∘ R`
  have eiso : CategoryTheory.Iso
      (CategoryTheory.Functor.comp
        (AlgebraicGeometry.Scheme.Modules.restrictFunctor (AlgebraicGeometry.Scheme.Opens.ι U))
        (Work.DSF1.Sheaf.sectionsFunctor U.toScheme (⊤ : U.toScheme.Opens)))
      (Work.DSF1.Sheaf.sectionsFunctor W.toScheme U) :=
    restrictIso_sectionsFunctor W.toScheme U
  have hcomp1 : (((Work.DSEQ0.sectionsV U.toScheme (⊤ : U.toScheme.Opens)).mapHomologicalComplex
        (ComplexShape.up ℕ)).obj K) ≅
      (((CategoryTheory.Functor.comp
        (AlgebraicGeometry.Scheme.Modules.restrictFunctor (AlgebraicGeometry.Scheme.Opens.ι U))
        (Work.DSF1.Sheaf.sectionsFunctor U.toScheme (⊤ : U.toScheme.Opens))).mapHomologicalComplex
          (ComplexShape.up ℕ)).obj I.cocomplex) :=
    (Functor.mapHomologicalComplexCompIso
      (CategoryTheory.Iso.refl (AlgebraicGeometry.Scheme.Modules.restrictFunctor
        (AlgebraicGeometry.Scheme.Opens.ι U) ⋙
        Work.DSF1.Sheaf.sectionsFunctor U.toScheme (⊤ : U.toScheme.Opens)))
      (ComplexShape.up ℕ)).app I.cocomplex
  have hcomp2 : (((CategoryTheory.Functor.comp
        (AlgebraicGeometry.Scheme.Modules.restrictFunctor (AlgebraicGeometry.Scheme.Opens.ι U))
        (Work.DSF1.Sheaf.sectionsFunctor U.toScheme (⊤ : U.toScheme.Opens))).mapHomologicalComplex
          (ComplexShape.up ℕ)).obj I.cocomplex) ≅
      ((Work.DSF1.Sheaf.sectionsFunctor W.toScheme U).mapHomologicalComplex
        (ComplexShape.up ℕ)).obj I.cocomplex :=
    (NatIso.mapHomologicalComplex eiso (ComplexShape.up ℕ)).app I.cocomplex
  have hcomp1' : ((HomologicalComplex.homologyFunctor AddCommGrpCat.{u} (ComplexShape.up ℕ) n).obj
        (((CategoryTheory.Functor.comp
          (AlgebraicGeometry.Scheme.Modules.restrictFunctor (AlgebraicGeometry.Scheme.Opens.ι U))
          (Work.DSF1.Sheaf.sectionsFunctor U.toScheme (⊤ : U.toScheme.Opens))).mapHomologicalComplex
            (ComplexShape.up ℕ)).obj I.cocomplex)) ≅
      ((HomologicalComplex.homologyFunctor AddCommGrpCat.{u} (ComplexShape.up ℕ) n).obj
        (((Work.DSEQ0.sectionsV U.toScheme (⊤ : U.toScheme.Opens)).mapHomologicalComplex
          (ComplexShape.up ℕ)).obj K)) :=
    ((HomologicalComplex.homologyFunctor AddCommGrpCat.{u} (ComplexShape.up ℕ) n).mapIso hcomp1).symm
  have hcomp2' : ((HomologicalComplex.homologyFunctor AddCommGrpCat.{u} (ComplexShape.up ℕ) n).obj
        (((Work.DSF1.Sheaf.sectionsFunctor W.toScheme U).mapHomologicalComplex
          (ComplexShape.up ℕ)).obj I.cocomplex)) ≅
      ((HomologicalComplex.homologyFunctor AddCommGrpCat.{u} (ComplexShape.up ℕ) n).obj
        (((CategoryTheory.Functor.comp
          (AlgebraicGeometry.Scheme.Modules.restrictFunctor (AlgebraicGeometry.Scheme.Opens.ι U))
          (Work.DSF1.Sheaf.sectionsFunctor U.toScheme (⊤ : U.toScheme.Opens))).mapHomologicalComplex
            (ComplexShape.up ℕ)).obj I.cocomplex)) :=
    ((HomologicalComplex.homologyFunctor AddCommGrpCat.{u} (ComplexShape.up ℕ) n).mapIso hcomp2).symm
  exact IsZero.of_iso (IsZero.of_iso hK1 hcomp1') hcomp2'

end Work.DSF1.Sheaf
