import Mathlib
import Submission.Work.ANALYTIC.CechPt.DHalf
import Submission.Work.ANALYTIC.CechPt.RHalf
import Submission.Work.ANALYTIC.CechPt.solidEquiv_cmpcpx
import Submission.Work.ANALYTIC.CechPt.dualCech_contractible
import Submission.Work.ANALYTIC.CechPt.IntervalAug

/-!
# The solid Čech complex of the Cantor cover is a resolution of `ℤ[∗]`

Assembly of the D-half of the Čech argument for the interval (`Work.ANALYTIC.profinite_HI_pt`).

* `Ks_comp_Ka`, `quasiIso_Ka` : the solid Čech complex `Dchain` (in `ℕ`-grading) of the Cantor
  cover is homotopy-equivalent to `ℤ[∗]` concentrated in degree `0`, so its augmentation `Ka` is a
  quasi-isomorphism.
* `augCan : Dcpx ⟶ ℤ[∗]`, its quasi-isomorphism/solid-equivalence, and its degree-`0` component
  `augCan_f_zero`.
* `cechAug_f_zero` and the comparison square `cmpcpx ≫ augCan = cechAugR ≫ single σ`.
-/

open CategoryTheory Limits LightProfinite LightCondensed MonoidalCategory MonoidalClosed
open _root_.LightCondensed _root_.LightCondensed.Solid
open Submission.Blueprint

noncomputable section

set_option linter.style.haveILetI false
set_option linter.unusedSimpArgs false

namespace Work.ANALYTIC.CechPt

open Work.ATOM

open scoped Simplicial

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

attribute [local implicit_reducible] Dchain
attribute [local implicit_reducible] Rchain
attribute [local implicit_reducible] ComplexShape.Embedding.extendFunctor
attribute [local implicit_reducible] HomologicalComplex.extend
attribute [local implicit_reducible] HomologicalComplex.single
attribute [local implicit_reducible] SimplicialObject.Augmented.whiskeringObj
attribute [local implicit_reducible] SimplicialObject.Augmented.whiskering
attribute [local implicit_reducible] CategoryTheory.Arrow.augmentedCechNerve
attribute [local implicit_reducible] cechNerve


/-! ## The homotopy equivalence `Dchain ≃ ℤ[∗]` -/

/-- The proof that `embeddingDownNat.f` sends `0` to `0`, with the index kept literal. -/
abbrev h0e : ComplexShape.embeddingDownNat.f (0:ℕ) = (0 : ℤ) := by norm_num

/-- `singleObjXSelf` of the `up ℤ`-graded single in degree `0` is the identity (the object in
degree `0` of the single is `A` definitionally). -/
lemma singleObjXSelf_up_zero (A : LightCondAb) :
    HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 A = Iso.refl A := rfl

/-- The inverse of `singleObjXSelf` of the `up ℤ`-graded single in degree `0` is the identity. -/
lemma singleObjXSelf_up_zero_inv (A : LightCondAb) :
    (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 A).inv = 𝟙 A := rfl

set_option backward.isDefEq.respectTransparency false in
/-- The section `Ks t₀` of the augmentation is a section. -/
theorem Ks_comp_Ka (t₀ : sd (zf (cechTerm 0)) ⟶ (𝟙_ LightCondAb))
    (ht0 : rho ≫ t₀ = 𝟙 (𝟙_ LightCondAb)) :
    Ks t₀ ≫ Ka = 𝟙 ((ChainComplex.single₀ LightCondAb).obj (zfree Work.ATOM.pt)) := by
  apply HomologicalComplex.from_single_hom_ext (j := (0 : ℕ))
  rw [HomologicalComplex.comp_f, Ks_f_zero, Ka_f_zero, HomologicalComplex.id_f]
  rw [Category.assoc, ← Category.assoc (f := Dsec t₀) (g := augZ)
    (h := (HomologicalComplex.singleObjXSelf (ComplexShape.down ℕ) 0
      (zfree Work.ATOM.pt)).inv)]
  rw [augZ_comp_Dsec t₀ ht0, Category.id_comp]
  exact Iso.hom_inv_id _

/-- The augmentation `Ka : Dchain ⟶ ℤ[∗]` is a quasi-isomorphism. -/
theorem quasiIso_Ka (t₀ : sd (zf (cechTerm 0)) ⟶ (𝟙_ LightCondAb))
    (t : ∀ q : ℕ, sd (zf (cechTerm (q+1))) ⟶ sd (zf (cechTerm q)))
    (ht0 : rho ≫ t₀ = 𝟙 (𝟙_ LightCondAb))
    (ht1 : dE 0 ≫ t 0 + t₀ ≫ rho = 𝟙 (sd (zf (cechTerm 0))))
    (ht2 : ∀ r : ℕ, dE (r+1) ≫ t (r+1) + t r ≫ dE r = 𝟙 (sd (zf (cechTerm (r+1))))) :
    QuasiIso Ka := by
  have hom := homotopy_Ka_Ks t₀ t ht0 ht1 ht2
  refine ⟨fun i => (quasiIsoAt_iff_isIso_homologyMap Ka i).2 ?_⟩
  have h1 : HomologicalComplex.homologyMap Ka i ≫
      HomologicalComplex.homologyMap (Ks t₀) i = 𝟙 (Dchain.homology i) := by
    rw [← HomologicalComplex.homologyMap_comp, hom.homologyMap_eq i,
      HomologicalComplex.homologyMap_id]
  have h2 : HomologicalComplex.homologyMap (Ks t₀) i ≫
      HomologicalComplex.homologyMap Ka i =
      𝟙 ((ChainComplex.single₀ LightCondAb |>.obj (zfree Work.ATOM.pt)).homology i) := by
    rw [← HomologicalComplex.homologyMap_comp, Ks_comp_Ka t₀ ht0,
      HomologicalComplex.homologyMap_id]
  exact ⟨⟨HomologicalComplex.homologyMap (Ks t₀) i, h1, h2⟩⟩

/-- The data of the contraction of the augmented dual Čech complex, which exists by
`Work.ANALYTIC.CechPt.dualCech_contractible`. -/
theorem exists_Hchain :
    ∃ (t₀ : sd (zf (cechTerm 0)) ⟶ (𝟙_ LightCondAb))
      (t : ∀ q : ℕ, sd (zf (cechTerm (q+1))) ⟶ sd (zf (cechTerm q))),
      (rho ≫ t₀ = 𝟙 (𝟙_ LightCondAb)) ∧
      (dE 0 ≫ t 0 + t₀ ≫ rho = 𝟙 (sd (zf (cechTerm 0)))) ∧
      (∀ r : ℕ, dE (r+1) ≫ t (r+1) + t r ≫ dE r = 𝟙 (sd (zf (cechTerm (r+1))))) :=
  dualCech_contractible

/-! ## The augmentation of the solid Čech complex in cochain form -/

/-- The augmentation of the solid Čech complex of the Cantor cover, in cochain form:
`Dcpx ⟶ ℤ[∗]` concentrated in degree `0`.

We write the source as the extension of `Dchain` by hand so that the declared type and the body
have *syntactically* equal objects. -/
noncomputable def augCan :
    HomologicalComplex.extend Dchain ComplexShape.embeddingDownNat ⟶
      (HomologicalComplex.single LightCondAb (ComplexShape.up ℤ) 0).obj
        (zfree Work.ATOM.pt) :=
  HomologicalComplex.extendMap Ka ComplexShape.embeddingDownNat ≫
    (HomologicalComplex.extendSingleIso ComplexShape.embeddingDownNat (zfree Work.ATOM.pt)
      0 0 (by simp)).hom

/-- `augCan` is a quasi-isomorphism: it is the extension of the quasi-isomorphism `Ka`. -/
theorem quasiIso_augCan (t₀ : sd (zf (cechTerm 0)) ⟶ (𝟙_ LightCondAb))
    (t : ∀ q : ℕ, sd (zf (cechTerm (q+1))) ⟶ sd (zf (cechTerm q)))
    (ht0 : rho ≫ t₀ = 𝟙 (𝟙_ LightCondAb))
    (ht1 : dE 0 ≫ t 0 + t₀ ≫ rho = 𝟙 (sd (zf (cechTerm 0))))
    (ht2 : ∀ r : ℕ, dE (r+1) ≫ t (r+1) + t r ≫ dE r = 𝟙 (sd (zf (cechTerm (r+1))))) :
    QuasiIso augCan := by
  haveI hK : QuasiIso Ka := quasiIso_Ka t₀ t ht0 ht1 ht2
  have h1 : QuasiIso (HomologicalComplex.extendMap Ka ComplexShape.embeddingDownNat) :=
    (HomologicalComplex.quasiIso_extendMap_iff Ka ComplexShape.embeddingDownNat).mpr hK
  have h2 : QuasiIso (HomologicalComplex.extendSingleIso ComplexShape.embeddingDownNat
      (zfree Work.ATOM.pt) 0 0 (by simp)).hom := inferInstance
  rw [augCan]
  exact (HomologicalComplex.quasiIso LightCondAb (ComplexShape.up ℤ)).comp_mem _ _ h1 h2

/-- `augCan` is a solid-equivalence. -/
theorem solidEquiv_augCan (t₀ : sd (zf (cechTerm 0)) ⟶ (𝟙_ LightCondAb))
    (t : ∀ q : ℕ, sd (zf (cechTerm (q+1))) ⟶ sd (zf (cechTerm q)))
    (ht0 : rho ≫ t₀ = 𝟙 (𝟙_ LightCondAb))
    (ht1 : dE 0 ≫ t 0 + t₀ ≫ rho = 𝟙 (sd (zf (cechTerm 0))))
    (ht2 : ∀ r : ℕ, dE (r+1) ≫ t (r+1) + t r ≫ dE r = 𝟙 (sd (zf (cechTerm (r+1))))) :
    SolidEquiv (DerivedCategory.Q.map augCan) :=
  (Work.TOOLKIT.toolkit_prop).of_iso _
    ((DerivedCategory.isIso_Q_map_iff_quasiIso LightCondAb augCan).mpr
      (quasiIso_augCan t₀ t ht0 ht1 ht2))

/-- The degree-`0` component of `augCan` is `augZ`. -/
theorem augCan_f_zero :
    augCan.f 0 = (HomologicalComplex.extendXIso Dchain ComplexShape.embeddingDownNat
      h0e).hom ≫ augZ := by
  have h : augCan.f 0 =
      (HomologicalComplex.extendXIso Dchain ComplexShape.embeddingDownNat
        h0e).hom ≫ augZD := by
    rw [augCan, HomologicalComplex.comp_f,
      HomologicalComplex.extendMap_f Ka ComplexShape.embeddingDownNat h0e,
      Ka_f_zero_D, HomologicalComplex.extendSingleIso_hom_f]
    simp only [Category.assoc]
    rw [Iso.inv_hom_id_assoc, Iso.inv_hom_id_assoc, singleObjXSelf_up_zero_inv]
    simp
  rw [h]
  rfl


/-! ## The point of light condensed sets is terminal -/

def point_terminal : IsTerminal (LightProfinite.toCondensed Work.ATOM.pt) :=
  LightProfinite.isTerminalPUnit.isTerminalObj lightProfiniteToLightCondSet _

/-! ## The comparison square -/

/-- **The augmentation of the interval**, as a morphism `ℤ[[0,1]] ⟶ ℤ[∗]` landing in the
`cechTerm` model of the point. -/
noncomputable def sigmaAug : (free ℤ).obj intervalCond ⟶ zfree Work.ATOM.pt :=
  freeLightCondAbOfTopFunctor.map termIC ≫
    (free ℤ).map (lightProfiniteToLightCondSetIsoTopCatToLightCondSet.inv.app Work.ATOM.pt)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency.types false in
/-- The degree-`0` component of `cechEps`: the augmentation of the free Čech complex. -/
lemma cechEps_f_zero {X : LightProfinite.{0}} {Y : LightCondSet.{0}}
    (β : LightProfinite.toCondensed X ⟶ Y) :
    (cechEps β).f 0 = (free ℤ).map (Limits.WidePullback.base (fun _ : Fin 1 => β)) := by
  simp only [cechEps, AlgebraicTopology.AlternatingFaceMapComplex.ε_app_f_zero,
    CategoryTheory.Arrow.augmentedCechNerve, SimplicialObject.Augmented.whiskeringObj]
  rfl

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency.types false in
/-- The degree-`0` component of the augmentation of a single complex is the augmenting map. -/
lemma single_map_f_zero {A B : LightCondAb} (f : A ⟶ B) :
    ((HomologicalComplex.single LightCondAb (ComplexShape.up ℤ) 0).map f).f 0 = f := by
  rw [HomologicalComplex.single_map_f_self, singleObjXSelf_up_zero, singleObjXSelf_up_zero]
  simp

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency.types false in
/-- The structure map `C_0 ⟶ Y` of the Čech nerve, in the `X 0`-presentation of the two sides. -/
noncomputable def cechBaseD {X : LightProfinite.{0}} {Y : LightCondSet.{0}}
    (β : LightProfinite.toCondensed X ⟶ Y) :
    (AlgebraicTopology.AlternatingFaceMapComplex.obj (cechNerve β ⋙ free ℤ)).X 0 ⟶
      ((ChainComplex.single₀ LightCondAb).obj ((free ℤ).obj Y)).X 0 :=
  (free ℤ).map (Limits.WidePullback.base (fun _ : Fin 1 => β))

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency.types false in
/-- The degree-`0` component of `cechEps`, with its two sides written in the `X 0`-presentation. -/
lemma cechEps_f_zero' {X : LightProfinite.{0}} {Y : LightCondSet.{0}}
    (β : LightProfinite.toCondensed X ⟶ Y) :
    (cechEps β).f 0 = cechBaseD β :=
  cechEps_f_zero β

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency.types false in
/-- The degree-`0` component of `cechAug`. -/
lemma cechAug_f_zero :
    (cechAug beta).f 0 =
      (HomologicalComplex.extendXIso dRLvlChain ComplexShape.embeddingDownNat h0e).hom ≫
      cechBaseD beta ≫
      (HomologicalComplex.singleObjXSelf (ComplexShape.down ℕ) 0
        ((free ℤ).obj intervalCond)).hom ≫
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
        ((free ℤ).obj intervalCond)).inv := by
  have h1 : (cechAug beta).f 0 =
      (HomologicalComplex.extendMap (cechEps beta) ComplexShape.embeddingDownNat).f 0 ≫
        (HomologicalComplex.extendSingleIso ComplexShape.embeddingDownNat
          ((free ℤ).obj intervalCond) 0 0 (by simp)).hom.f 0 :=
    HomologicalComplex.comp_f _ _ 0
  have h2 : (HomologicalComplex.extendMap (cechEps beta) ComplexShape.embeddingDownNat).f 0 =
      (HomologicalComplex.extendXIso dRLvlChain ComplexShape.embeddingDownNat h0e).hom ≫
      (cechEps beta).f 0 ≫
      (HomologicalComplex.extendXIso ((ChainComplex.single₀ LightCondAb).obj
        ((free ℤ).obj intervalCond)) ComplexShape.embeddingDownNat h0e).inv :=
    HomologicalComplex.extendMap_f (cechEps beta) ComplexShape.embeddingDownNat h0e
  have h3 : (cechEps beta).f 0 = cechBaseD beta :=
    cechEps_f_zero' beta
  have h4 : (HomologicalComplex.extendSingleIso ComplexShape.embeddingDownNat
        ((free ℤ).obj intervalCond) 0 0 (by simp)).hom.f 0 =
      (HomologicalComplex.extendXIso ((ChainComplex.single₀ LightCondAb).obj
        ((free ℤ).obj intervalCond)) ComplexShape.embeddingDownNat h0e).hom ≫
      (HomologicalComplex.singleObjXSelf (ComplexShape.down ℕ) 0
        ((free ℤ).obj intervalCond)).hom ≫
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
        ((free ℤ).obj intervalCond)).inv := by
    rw [HomologicalComplex.extendSingleIso_hom_f]
  rw [h1, h2, h3, h4]
  simp only [Category.assoc]
  rw [Iso.inv_hom_id_assoc]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency.types false in
/-- The degree-`0` component of the isomorphism `cpxIso`. -/
lemma cpxIso_hom_f_zero :
    (cpxIso.hom).f 0 =
      (HomologicalComplex.extendXIso Rchain ComplexShape.embeddingDownNat h0e).hom ≫
      (free ℤ).map (cechCompare 0) ≫
      (HomologicalComplex.extendXIso dRLvlChain ComplexShape.embeddingDownNat h0e).inv := by
  have h1 : (cpxIso.hom).f 0 =
      (HomologicalComplex.extendXIso Rchain ComplexShape.embeddingDownNat h0e).hom ≫
      (chainIso.hom).f 0 ≫
      (HomologicalComplex.extendXIso dRLvlChain ComplexShape.embeddingDownNat h0e).inv :=
    HomologicalComplex.extendMap_f chainIso.hom ComplexShape.embeddingDownNat h0e
  have h2 : (chainIso.hom).f 0 = (free ℤ).map (cechCompare 0) := by
    rw [show (chainIso.hom).f 0 = (dRLvlIso' 0).hom from rfl, dRLvlIso', Iso.trans_hom,
      dRLvlIso_hom]
    simp only [Category.assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id, Category.comp_id]
  rw [h1, h2]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency.types false in
/-- The degree-`0` component of `cechAugR`. -/
lemma cechAugR_f_zero :
    cechAugR.f 0 =
      (HomologicalComplex.extendXIso Rchain ComplexShape.embeddingDownNat h0e).hom ≫
      ((free ℤ).map (lightProfiniteToLightCondSet.map (cechProj 0 0) ≫ beta) :
        Rchain.X 0 ⟶ (free ℤ).obj intervalCond) ≫
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
        ((free ℤ).obj intervalCond)).inv := by
  have h1 : cechAugR.f 0 = (cpxIso.hom).f 0 ≫ (cechAug beta).f 0 :=
    HomologicalComplex.comp_f cpxIso.hom (cechAug beta) 0
  have hcb : (free ℤ).map (cechCompare 0) ≫
        (free ℤ).map (Limits.WidePullback.base (fun _ : Fin 1 => beta)) =
      (free ℤ).map (lightProfiniteToLightCondSet.map (cechProj 0 0) ≫ beta) := by
    rw [← Functor.map_comp, cechCompare_base]
  rw [h1, cpxIso_hom_f_zero, cechAug_f_zero]
  simp only [Category.assoc]
  rw [Iso.inv_hom_id_assoc]
  rw [cechBaseD]
  rw [← Category.assoc (f := (free ℤ).map (cechCompare 0))
    (g := (free ℤ).map (Limits.WidePullback.base (fun _ : Fin 1 => beta)))]
  rw [hcb]
  rw [ChainComplex.single₀ObjXSelf, Iso.refl_hom, Category.id_comp]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency.types false in
/-- The degree-`0` component of the comparison `cmpcpx`. -/
lemma cmpcpx_f_zero :
    cmpcpx.f 0 =
      (HomologicalComplex.extendXIso Rchain ComplexShape.embeddingDownNat h0e).hom ≫
      doubleDualUnit (zf (cechTerm 0)) ≫
      (HomologicalComplex.extendXIso Dchain ComplexShape.embeddingDownNat h0e).inv :=
  cmpcpx_f_neg 0

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency.types false in
/-- The equality of maps of light condensed sets underlying the comparison square. -/
lemma toPt_eq : (lightProfiniteToLightCondSet.map (toPt (cechTerm 0)) :
      LightProfinite.toCondensed (cechTerm 0) ⟶ LightProfinite.toCondensed Work.ATOM.pt) =
    lightProfiniteToLightCondSet.map (cechProj 0 0) ≫ beta ≫
      (topCatToLightCondSet.map termIC ≫
        lightProfiniteToLightCondSetIsoTopCatToLightCondSet.inv.app Work.ATOM.pt) :=
  IsTerminal.hom_ext point_terminal _ _

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency.types false in
/-- The `zmap`-level form of `toPt_eq`, which is the degree-`0` identity needed for the square. -/
lemma zmapToPt_eq :
    zmap (toPt (cechTerm 0)) =
      (free ℤ).map (lightProfiniteToLightCondSet.map (cechProj 0 0) ≫ beta) ≫ sigmaAug := by
  have h1 : zmap (toPt (cechTerm 0)) =
      (free ℤ).map (lightProfiniteToLightCondSet.map (toPt (cechTerm 0))) := rfl
  have h2 : (free ℤ).map (lightProfiniteToLightCondSet.map (cechProj 0 0) ≫ beta) ≫ sigmaAug =
      (free ℤ).map (lightProfiniteToLightCondSet.map (cechProj 0 0) ≫ beta ≫
        (topCatToLightCondSet.map termIC ≫
          lightProfiniteToLightCondSetIsoTopCatToLightCondSet.inv.app Work.ATOM.pt)) := by
    rw [sigmaAug, show freeLightCondAbOfTopFunctor.map termIC =
      (free ℤ).map (topCatToLightCondSet.map termIC) from rfl, ← Functor.map_comp,
      ← Functor.map_comp, Category.assoc]
  rw [h1, h2, toPt_eq]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency.types false in
/-- **The comparison square**: the two ways of resolving `ℤ[∗]` by the free Čech complex of the
Cantor cover agree. -/
theorem cmpcpx_augCan_eq :
    cmpcpx ≫ augCan = cechAugR ≫
      (HomologicalComplex.single LightCondAb (ComplexShape.up ℤ) 0).map sigmaAug := by
  apply HomologicalComplex.to_single_hom_ext (j := (0 : ℤ))
  rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f, cmpcpx_f_zero, augCan_f_zero,
    cechAugR_f_zero, single_map_f_zero]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  rw [doubleDualUnit_augZ, singleObjXSelf_up_zero_inv, Category.id_comp, zmapToPt_eq]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency.types false in
/-- **Two-out-of-three**: the augmentation `ℤ[[0,1]] ⟶ ℤ[∗]` of the interval (transported to the
`cechTerm`-model point) is a solid-equivalence. -/
theorem solidEquiv_sigmaAug
    (hmu : ∀ T : LightProfinite.{0}, SolidEquiv
      ((DerivedCategory.singleFunctor LightCondAb 0).map (doubleDualUnit (zf T))))
    (t₀ : sd (zf (cechTerm 0)) ⟶ (𝟙_ LightCondAb))
    (t : ∀ q : ℕ, sd (zf (cechTerm (q+1))) ⟶ sd (zf (cechTerm q)))
    (ht0 : rho ≫ t₀ = 𝟙 (𝟙_ LightCondAb))
    (ht1 : dE 0 ≫ t 0 + t₀ ≫ rho = 𝟙 (sd (zf (cechTerm 0))))
    (ht2 : ∀ r : ℕ, dE (r+1) ≫ t (r+1) + t r ≫ dE r = 𝟙 (sd (zf (cechTerm (r+1))))) :
    SolidEquiv ((DerivedCategory.singleFunctor LightCondAb 0).map sigmaAug) := by
  have hR : SolidEquiv (DerivedCategory.Q.map cechAugR) := solidEquiv_cechAugR
  have hD : SolidEquiv (DerivedCategory.Q.map augCan) := solidEquiv_augCan t₀ t ht0 ht1 ht2
  have hcmp : SolidEquiv (DerivedCategory.Q.map cmpcpx) := solidEquiv_cmpcpx hmu
  have hsq : DerivedCategory.Q.map cmpcpx ≫ DerivedCategory.Q.map augCan =
      DerivedCategory.Q.map cechAugR ≫ DerivedCategory.Q.map
        ((HomologicalComplex.single LightCondAb (ComplexShape.up ℤ) 0).map sigmaAug) := by
    rw [← Functor.map_comp, ← Functor.map_comp, cmpcpx_augCan_eq]
  have h1 : SolidEquiv (DerivedCategory.Q.map cechAugR ≫ DerivedCategory.Q.map
      ((HomologicalComplex.single LightCondAb (ComplexShape.up ℤ) 0).map sigmaAug)) := by
    rw [← hsq]
    exact (Work.TOOLKIT.toolkit_prop).comp _ _ hcmp hD
  have h2 : SolidEquiv (DerivedCategory.Q.map
      ((HomologicalComplex.single LightCondAb (ComplexShape.up ℤ) 0).map sigmaAug)) :=
    (Work.TOOLKIT.toolkit_prop).of_comp_left _ _ hR h1
  rwa [DerivedCategory.Q_map_single_map] at h2

end Work.ANALYTIC.CechPt
