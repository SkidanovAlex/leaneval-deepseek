import Mathlib
import Submission.Work.ANALYTIC.CechPt.DdZfAux
import Submission.Work.ANALYTIC.pi_option_iso_biprod
import Submission.Work.ANALYTIC.ihom_coprod_iso

/-!
# The assembly of `ddZf_iso_prod` from its pieces

This module contains the (pure category theory + `haar_basisIso`) assembly of
`Work.ANALYTIC.CechPt.ddZf_iso_prod` from the five pieces

* `gamma_phiT` (`Submission/Work/ANALYTIC/CechPt/gamma_phiT.lean`),
* `lamHat_lamJ` (`.../lamHat_lamJ.lean`),
* `lamHat_lamInf` (`.../lamHat_lamInf.lean`),
* `cdisc_coproduct_basis` (`.../cdisc_coproduct_basis.lean`),
* `isIso_piLift_pre_sigma_unit` (`.../isIso_piLift_pre_sigma_unit.lean`),

stated here as hypotheses (`exists_coproduct_phiOf`, `isIso_ddProjMap`,
`ddZf_iso_prod_of_pieces`).
-/

open CategoryTheory Limits LightProfinite LightCondensed MonoidalCategory MonoidalClosed
open _root_.LightCondensed _root_.LightCondensed.Solid
open Opposite OnePoint

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace Work.ANALYTIC.CechPt

section PiOnePoint

/-- The `∞`-coordinate of `piOnePointIsoProd : ∏_{ℕ∪∞} ℤ ≅ ℤ ⨯ ∏_ℕ ℤ`. -/
theorem piOnePointIsoProd_hom_fst :
    piOnePointIsoProd.hom ≫ prod.fst =
      Pi.π (fun _ : OnePoint ℕ => Work.ANALYTIC.Z) (∞ : OnePoint ℕ) :=
  IsLimit.conePointUniqueUpToIso_hom_comp
    (productIsProduct (fun _ : OnePoint ℕ => Work.ANALYTIC.Z)) isLimit_optionFan
    (Discrete.mk (∞ : OnePoint ℕ))

/-- The `n`-coordinate of `piOnePointIsoProd : ∏_{ℕ∪∞} ℤ ≅ ℤ ⨯ ∏_ℕ ℤ`. -/
theorem piOnePointIsoProd_hom_snd (n : ℕ) :
    piOnePointIsoProd.hom ≫ prod.snd ≫
        Pi.π (fun _ : ℕ => Work.ANALYTIC.Z) n =
      Pi.π (fun _ : OnePoint ℕ => Work.ANALYTIC.Z) (OnePoint.some n) := by
  have h2 : piOnePointIsoProd.hom ≫ prod.snd ≫ Pi.π (fun _ : ℕ => Work.ANALYTIC.Z) n =
      piOnePointIsoProd.hom ≫ (optionFan.proj (OnePoint.some n)) := by
    rw [optionFan_proj, optionProj_some]
  rw [h2]
  exact IsLimit.conePointUniqueUpToIso_hom_comp
    (productIsProduct (fun _ : OnePoint ℕ => Work.ANALYTIC.Z)) isLimit_optionFan
    (Discrete.mk (OnePoint.some n))

/-- The `fst`-coordinate of `(biprod.isoProd Z prodZ).inv`. -/
theorem biprodIsoProd_inv_fst : (biprod.isoProd Z Work.ANALYTIC.prodZ).inv ≫
    CategoryTheory.Limits.biprod.fst = prod.fst := by
  rw [biprod.isoProd_inv, biprod.lift_fst]

/-- The `snd`-coordinates of `(biprod.isoProd Z prodZ).inv`. -/
theorem biprodIsoProd_inv_snd (j : ℕ) :
    (biprod.isoProd Z Work.ANALYTIC.prodZ).inv ≫
      CategoryTheory.Limits.biprod.snd ≫ CategoryTheory.Limits.Pi.π (fun _ : ℕ => Z) j =
    prod.snd ≫ CategoryTheory.Limits.Pi.π (fun _ : ℕ => Z) j := by
  rw [biprod.isoProd_inv, ← Category.assoc, biprod.lift_snd]

end PiOnePoint

/-- The point-section map of an isomorphism is injective. -/
theorem injective_pointSection_of_iso {A B : LightCondAb} (e : A ≅ B) :
    Function.Injective ((e.hom).hom.app (Opposite.op Work.ATOM.pt)) := by
  intro x y hxy
  have hid : ∀ z : ↥((A).obj.obj (Opposite.op Work.ATOM.pt)),
      ((e.inv).hom.app (Opposite.op Work.ATOM.pt))
        (((e.hom).hom.app (Opposite.op Work.ATOM.pt)) z) = z := by
    intro z
    have h := congrArg (fun (k : A ⟶ A) => (k.hom.app (Opposite.op Work.ATOM.pt)) z)
      (Iso.hom_inv_id e)
    simpa only [ObjectProperty.FullSubcategory.comp_hom, ObjectProperty.FullSubcategory.id_hom,
      NatTrans.comp_app, NatTrans.id_app, ModuleCat.hom_id,
      ConcreteCategory.comp_apply, ConcreteCategory.id_apply, LinearMap.id_apply] using h
  have h2 : ((e.inv).hom.app (Opposite.op Work.ATOM.pt))
        (((e.hom).hom.app (Opposite.op Work.ATOM.pt)) x) =
      ((e.inv).hom.app (Opposite.op Work.ATOM.pt))
        (((e.hom).hom.app (Opposite.op Work.ATOM.pt)) y) := by rw [hxy]
  rwa [hid x, hid y] at h2

/-- **(A) The dual elements are the coproduct injections.**  From the identification of `phiT` with
the evaluation pairing (`hgamma`), the identification of the dual elements with the Haar basis
(`hJ`, `hInf`) and the coproduct description of `Cdisc T` (`hbasis`), the family
`phiOf (zf T) (dualElement T j)` exhibits `sd (zf T)` as the coproduct `∐_j 𝟙`. -/
theorem exists_coproduct_phiOf (T : LightProfinite.{0}) [Infinite T]
    (hgamma : ∀ lam : zf T ⟶ Z,
      Work.ATOM.toPointEquiv (Work.ANALYTIC.Cdisc T)
          (CategoryTheory.CategoryStruct.comp (phiOf (zf T) lam) (phiT T).hom) =
        LocallyConstant.const ↥(Work.ATOM.pt.toTop) (lamHat T lam))
    (hJ : ∀ n : ℕ, lamHat T (lamJ T n) = Haar.fCyl T n)
    (hInf : lamHat T (lamInf T) = 1)
    (hbasis : ∃ Θ : Work.ANALYTIC.Cdisc T ≅ ∐ (fun _ : Haar.JIdx => Z),
      ∀ j : Haar.JIdx,
        Work.ATOM.toPointEquiv (Work.ANALYTIC.Cdisc T)
          (CategoryTheory.CategoryStruct.comp
            (Sigma.ι (fun _ : Haar.JIdx => Z) j) Θ.inv) =
        LocallyConstant.const ↥(Work.ATOM.pt.toTop) (Haar.fJ T j)) :
    ∃ Φ : (∐ (fun _ : Haar.JIdx => Z)) ≅ sd (zf T),
      ∀ j : Haar.JIdx,
        CategoryTheory.CategoryStruct.comp (Sigma.ι (fun _ : Haar.JIdx => Z) j) Φ.hom =
          phiOf (zf T) (dualElement T j) := by
  obtain ⟨Θ, hΘ⟩ := hbasis
  let Φ : (∐ (fun _ : Haar.JIdx => Z)) ≅ sd (zf T) := Θ.symm ≪≫ (phiT T).symm
  refine ⟨Φ, fun j => ?_⟩
  apply (Work.ATOM.toPointEquiv (sd (zf T))).injective
  apply injective_pointSection_of_iso (phiT T)
  rw [← Work.ATOM.toPointEquiv_naturality (h := (phiT T).hom)
      (u := CategoryTheory.CategoryStruct.comp (Sigma.ι (fun _ : Haar.JIdx => Z) j) Φ.hom),
    ← Work.ATOM.toPointEquiv_naturality (h := (phiT T).hom)
      (u := phiOf (zf T) (dualElement T j))]
  have h1 : Work.ATOM.toPointEquiv (Work.ANALYTIC.Cdisc T)
      (CategoryTheory.CategoryStruct.comp
        (CategoryTheory.CategoryStruct.comp (Sigma.ι (fun _ : Haar.JIdx => Z) j) Φ.hom)
        (phiT T).hom) =
      LocallyConstant.const ↥(Work.ATOM.pt.toTop) (Haar.fJ T j) := by
    have hcomp : CategoryTheory.CategoryStruct.comp
        (CategoryTheory.CategoryStruct.comp (Sigma.ι (fun _ : Haar.JIdx => Z) j) Φ.hom)
        (phiT T).hom =
        CategoryTheory.CategoryStruct.comp (Sigma.ι (fun _ : Haar.JIdx => Z) j) Θ.inv := by
      show CategoryTheory.CategoryStruct.comp (CategoryTheory.CategoryStruct.comp _ Φ.hom) _ = _
      rw [show Φ.hom = CategoryTheory.CategoryStruct.comp Θ.inv (phiT T).inv from rfl]
      simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rw [hcomp, hΘ j]
  rw [h1, hgamma (dualElement T j)]
  congr 1
  induction j using OnePoint.rec with
  | infty =>
      show Haar.fJ T Haar.inf = lamHat T (lamInf T)
      rw [Haar.fJ_inf, hInf]
  | coe n =>
      show Haar.fJ T (n : Haar.JIdx) = lamHat T (lamJ T n)
      rw [Haar.fJ_coe, hJ n]

/-- **(B) The comparison map `ddProjMap` is an isomorphism**, given that the dual elements are the
coproduct injections. -/
theorem isIso_ddProjMap (T : LightProfinite.{0}) [Infinite T]
    (hS3 : CategoryTheory.IsIso (CategoryTheory.Limits.Pi.lift (fun j : Haar.JIdx =>
      CategoryTheory.CategoryStruct.comp
        ((CategoryTheory.MonoidalClosed.pre
          (CategoryTheory.Limits.Sigma.ι (fun _ : Haar.JIdx => Z) j)).app Z)
        (CategoryTheory.MonoidalClosed.unitIsoSelf Z).hom)))
    (hΦ : ∃ Φ : (∐ (fun _ : Haar.JIdx => Z)) ≅ sd (zf T),
      ∀ j : Haar.JIdx,
        CategoryTheory.CategoryStruct.comp (Sigma.ι (fun _ : Haar.JIdx => Z) j) Φ.hom =
          phiOf (zf T) (dualElement T j)) :
    IsIso (ddProjMap T) := by
  obtain ⟨Φ, hΦ⟩ := hΦ
  haveI hpre : IsIso (MonoidalClosed.pre Φ.hom) :=
    ⟨⟨MonoidalClosed.pre Φ.inv, by rw [← MonoidalClosed.pre_map, Iso.inv_hom_id,
        MonoidalClosed.pre_id], by rw [← MonoidalClosed.pre_map, Iso.hom_inv_id,
        MonoidalClosed.pre_id]⟩⟩
  haveI hpreApp : IsIso ((MonoidalClosed.pre Φ.hom).app (𝟙_ LightCondAb)) := inferInstance
  haveI hpi : IsIso (CategoryTheory.Limits.Pi.lift (fun j : Haar.JIdx =>
      CategoryTheory.CategoryStruct.comp
        ((CategoryTheory.MonoidalClosed.pre
          (CategoryTheory.Limits.Sigma.ι (fun _ : Haar.JIdx => Z) j)).app Z)
        (CategoryTheory.MonoidalClosed.unitIsoSelf Z).hom)) := hS3
  have hcomp : ddProjMap T = CategoryTheory.CategoryStruct.comp
      ((MonoidalClosed.pre Φ.hom).app (𝟙_ LightCondAb))
      (CategoryTheory.Limits.Pi.lift (fun j : Haar.JIdx =>
        CategoryTheory.CategoryStruct.comp
          ((CategoryTheory.MonoidalClosed.pre
            (CategoryTheory.Limits.Sigma.ι (fun _ : Haar.JIdx => Z) j)).app Z)
          (CategoryTheory.MonoidalClosed.unitIsoSelf Z).hom)) := by
    apply Limits.Pi.hom_ext
    intro j
    rw [ddProjMap_π, Category.assoc]
    erw [Limits.Pi.lift_comp_π]
    rw [coordMap_eq_pre_phiOf, ← hΦ j, MonoidalClosed.pre_map,
      CategoryTheory.NatTrans.comp_app]
    rfl
  rw [hcomp]
  exact IsIso.comp_isIso' hpreApp hpi

/-- **The main assembly.**  Given the five pieces, `dd (ℤ[T])` is the biproduct `𝟙 ⊞ ∏ℤ` with the
prescribed coordinates. -/
theorem ddZf_iso_prod_of_pieces (T : LightProfinite.{0}) [Infinite T]
    (hgamma : ∀ lam : zf T ⟶ Z,
      Work.ATOM.toPointEquiv (Work.ANALYTIC.Cdisc T)
          (CategoryTheory.CategoryStruct.comp (phiOf (zf T) lam) (phiT T).hom) =
        LocallyConstant.const ↥(Work.ATOM.pt.toTop) (lamHat T lam))
    (hJ : ∀ n : ℕ, lamHat T (lamJ T n) = Haar.fCyl T n)
    (hInf : lamHat T (lamInf T) = 1)
    (hbasis : ∃ Θ : Work.ANALYTIC.Cdisc T ≅ ∐ (fun _ : Haar.JIdx => Z),
      ∀ j : Haar.JIdx,
        Work.ATOM.toPointEquiv (Work.ANALYTIC.Cdisc T)
          (CategoryTheory.CategoryStruct.comp
            (Sigma.ι (fun _ : Haar.JIdx => Z) j) Θ.inv) =
        LocallyConstant.const ↥(Work.ATOM.pt.toTop) (Haar.fJ T j))
    (hS3 : CategoryTheory.IsIso (CategoryTheory.Limits.Pi.lift (fun j : Haar.JIdx =>
      CategoryTheory.CategoryStruct.comp
        ((CategoryTheory.MonoidalClosed.pre
          (CategoryTheory.Limits.Sigma.ι (fun _ : Haar.JIdx => Z) j)).app Z)
        (CategoryTheory.MonoidalClosed.unitIsoSelf Z).hom))) :
    ∃ e : Work.ANALYTIC.CechPt.dd (Work.ANALYTIC.CechPt.zf T) ≅
        (Z ⊞ Work.ANALYTIC.prodZ),
      (e.hom ≫ CategoryTheory.Limits.biprod.fst =
        Work.ANALYTIC.CechPt.coordMap (Work.ANALYTIC.CechPt.zf T)
          (Work.ANALYTIC.CechPt.lamInf T)) ∧
      (∀ j : ℕ, e.hom ≫ CategoryTheory.Limits.biprod.snd ≫
          CategoryTheory.Limits.Pi.π (fun _ : ℕ => Z) j =
        Work.ANALYTIC.CechPt.coordMap (Work.ANALYTIC.CechPt.zf T)
          (Work.ANALYTIC.CechPt.lamJ T j)) := by
  haveI hdd : IsIso (ddProjMap T) :=
    isIso_ddProjMap T hS3 (exists_coproduct_phiOf T hgamma hJ hInf hbasis)
  let e : dd (zf T) ≅ (Z ⊞ Work.ANALYTIC.prodZ) :=
    (asIso (ddProjMap T)).trans (piOnePointIsoProd.trans (biprod.isoProd Z prodZ).symm)
  have he : e.hom = ddProjMap T ≫ piOnePointIsoProd.hom ≫ (biprod.isoProd Z prodZ).inv := by
    simp only [e, Iso.trans_hom, Iso.symm_hom, asIso_hom]
  refine ⟨e, ?_, ?_⟩
  · -- the `∞`-coordinate
    show e.hom ≫ CategoryTheory.Limits.biprod.fst = coordMap (zf T) (lamInf T)
    rw [he]
    simp only [Category.assoc]
    rw [biprodIsoProd_inv_fst, piOnePointIsoProd_hom_fst, ddProjMap_π, dualElement_infty]
  · intro j
    show e.hom ≫ CategoryTheory.Limits.biprod.snd ≫
      CategoryTheory.Limits.Pi.π (fun _ : ℕ => Z) j = coordMap (zf T) (lamJ T j)
    rw [he]
    simp only [Category.assoc]
    rw [biprodIsoProd_inv_snd j, piOnePointIsoProd_hom_snd, ddProjMap_π, dualElement_coe]

end Work.ANALYTIC.CechPt
