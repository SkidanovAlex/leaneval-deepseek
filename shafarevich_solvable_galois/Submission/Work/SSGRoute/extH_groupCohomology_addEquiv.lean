import Mathlib
import Submission.Work.SSGRoute.PTDefs
import Submission.Work.SSGRoute.E0bBarChange
import Submission.Work.SSGRoute.e0b_bridge
import Submission.Work.SSGRoute.E0bGroupCoeffDefs
import Submission.Work.SSGRoute.cochainsMap_inhomogeneousCochainsIso_comm
import Submission.Work.SSGRoute.bridgeE_map_coeff
import Submission.Work.SSGRoute.E0bGC.mapExtAddHom_extMk
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

open CategoryTheory
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

namespace Work.SSGRoute.E0bGroupCoeff

open SSGRoute.PTExt
open scoped Classical

noncomputable section

/-! ## The bridge -/

def eTheta (n : ℕ) (G : Type) [Group G] (A : Rep.{0, 0, 0} Coeff G) :
    groupCohomology A n ≃+ ((Rep.barComplex Coeff G).linearYonedaObj Coeff A).homology n :=
  ((HomologicalComplex.homologyMapIso (groupCohomology.inhomogeneousCochainsIso A) n).toLinearEquiv).toAddEquiv

def eBridge (n : ℕ) (G : Type) [Group G] (A : Rep.{0, 0, 0} Coeff G) :
    groupCohomology A n ≃+ SSGRoute.PTExt.extH A n :=
  (eTheta n G A).trans (Bridge.Psi n G A)

lemma eBridge_apply (n : ℕ) (G : Type) [Group G] (A : Rep.{0, 0, 0} Coeff G)
    (x : groupCohomology A n) :
    eBridge n G A x = Bridge.Psi n G A
      (HomologicalComplex.homologyMap (groupCohomology.inhomogeneousCochainsIso A).hom n x) := rfl

/-! ## The group-change chain map, in the `barRes` spelling -/

def lyBar {G H : Type} [Group G] [Group H] (f : H →* G)
    {A : Rep.{0, 0, 0} Coeff G} {B : Rep.{0, 0, 0} Coeff H} (φ : Rep.res f A ⟶ B) :
    ((Bridge.barRes G).complex.linearYonedaObj Coeff A) ⟶
      ((Bridge.barRes H).complex.linearYonedaObj Coeff B) :=
  E0bGC.lyMap Coeff f φ

lemma lyBar_f_apply {G H : Type} [Group G] [Group H] (f : H →* G)
    {A : Rep.{0, 0, 0} Coeff G} {B : Rep.{0, 0, 0} Coeff H} (φ : Rep.res f A ⟶ B) (n : ℕ)
    (g : (Rep.barComplex Coeff G).X n ⟶ A) :
    (lyBar f φ).f n g = SSGRoute.PTExt.barChange Coeff G H f n ≫
      (Rep.resFunctor f).map g ≫ φ := by
  change (E0bGC.lyMap Coeff f φ).f n g = _
  rw [E0bGC.lyMap_f_apply]

/-! ## Auxiliary cycle computations -/

lemma iCycles_cocycle (n : ℕ) (G : Type) [Group G] (A : Rep.{0, 0, 0} Coeff G)
    (c : ((Bridge.barRes G).complex.linearYonedaObj Coeff A).cycles n) :
    (Rep.barComplex Coeff G).d (n + 1) n ≫
      ((Bridge.barRes G).complex.linearYonedaObj Coeff A).iCycles n c = 0 := by
  have hcoc : (ConcreteCategory.hom
      (((Bridge.barRes G).complex.linearYonedaObj Coeff A).d n (n + 1)))
      (((Bridge.barRes G).complex.linearYonedaObj Coeff A).iCycles n c) = 0 :=
    ConcreteCategory.congr_hom (HomologicalComplex.iCycles_d
      ((Bridge.barRes G).complex.linearYonedaObj Coeff A) n (n + 1)) c
  rwa [Work.SSGRoute.E0bCore.linearYonedaObj_d_apply (k := Coeff) (i := n) (j := n + 1)
    (Bridge.barRes G).complex A rfl _] at hcoc

lemma Psi_apply_cycle (n : ℕ) (G : Type) [Group G] (A : Rep.{0, 0, 0} Coeff G)
    (z : ((Bridge.barRes G).complex.linearYonedaObj Coeff A).cycles n) :
    Bridge.Psi n G A
        (HomologicalComplex.homologyπ ((Bridge.barRes G).complex.linearYonedaObj Coeff A) n z) =
      (Bridge.barRes G).extMk
        (Work.SSGRoute.E0bCore.cycHom (Bridge.barRes G) n z) (n + 1) rfl
        (Work.SSGRoute.E0bCore.cycHom_cocycle (Bridge.barRes G) n z) := by
  rw [Bridge_Psi_eq n G A]
  exact PsiOf_homologyπ_apply Coeff (Bridge.barRes G) n z

lemma iCycles_cyclesMap_gen {K L : CochainComplex (ModuleCat Coeff) ℕ} (U : K ⟶ L) (n : ℕ)
    (c : K.cycles n) :
    (HomologicalComplex.iCycles L n) (HomologicalComplex.cyclesMap U n c) =
      U.f n ((HomologicalComplex.iCycles K n) c) := by
  have h := congrArg (fun (g : K.cycles n ⟶ L.X n) => g c)
    (HomologicalComplex.cyclesMap_i U n)
  simpa only [ConcreteCategory.comp_apply] using h

lemma Psi_homologyMap_homologypi (n : ℕ) (G : Type) [Group G] (A : Rep.{0, 0, 0} Coeff G)
    {K : CochainComplex (ModuleCat Coeff) ℕ}
    (U : K ⟶ ((Bridge.barRes G).complex.linearYonedaObj Coeff A)) (c : K.cycles n)
    (hc : (Bridge.barRes G).complex.d (n + 1) n ≫ (U.f n (K.iCycles n c)) = 0) :
    Bridge.Psi n G A (HomologicalComplex.homologyMap U n (K.homologyπ n c)) =
      (Bridge.barRes G).extMk (U.f n (K.iCycles n c)) (n + 1) rfl hc := by
  have hnat : HomologicalComplex.homologyMap U n (K.homologyπ n c) =
      HomologicalComplex.homologyπ ((Bridge.barRes G).complex.linearYonedaObj Coeff A) n
        (HomologicalComplex.cyclesMap U n c) := by
    have h := congrArg (fun (g : K.cycles n ⟶
        ((Bridge.barRes G).complex.linearYonedaObj Coeff A).homology n) => g c)
      (HomologicalComplex.homologyπ_naturality U n)
    simpa only [ConcreteCategory.comp_apply] using h
  rw [hnat, Psi_apply_cycle n G A (HomologicalComplex.cyclesMap U n c)]
  refine Work.SSGRoute.E0bCore.extMk_congr (Bridge.barRes G) ?_ _ _
  rw [← Work.SSGRoute.E0bCore.iCycles_eq_cycHom (Bridge.barRes G) n
    (HomologicalComplex.cyclesMap U n c)]
  rw [iCycles_cyclesMap_gen U n c]

/-! ## The cocycle condition along the group change -/

lemma barChange_cocycle {G H : Type} [Group G] [Group H] (f : H →* G)
    {A : Rep.{0, 0, 0} Coeff G} (n : ℕ) (g : (Rep.barComplex Coeff G).X n ⟶ A)
    (hg : (Rep.barComplex Coeff G).d (n + 1) n ≫ g = 0) :
    (Rep.barComplex Coeff H).d (n + 1) n ≫
      (SSGRoute.PTExt.barChange Coeff G H f n ≫ (Rep.resFunctor f).map g) = 0 := by
  have hchain := SSGRoute.PTExt.barChange_chain (k := Coeff) G H f n
  rw [Rep.barComplex.d_def (k := Coeff) (G := H)]
  calc Rep.barComplex.d Coeff H n ≫
        (SSGRoute.PTExt.barChange Coeff G H f n ≫ (Rep.resFunctor f).map g)
      = (Rep.barComplex.d Coeff H n ≫ SSGRoute.PTExt.barChange Coeff G H f n) ≫
          (Rep.resFunctor f).map g := by simp only [Category.assoc]
    _ = (SSGRoute.PTExt.barChange Coeff G H f (n + 1) ≫
          (Rep.resFunctor f).map (Rep.barComplex.d Coeff G n)) ≫
          (Rep.resFunctor f).map g := by rw [← hchain]
    _ = SSGRoute.PTExt.barChange Coeff G H f (n + 1) ≫
          ((Rep.resFunctor f).map (Rep.barComplex.d Coeff G n) ≫
            (Rep.resFunctor f).map g) := by simp only [Category.assoc]
    _ = SSGRoute.PTExt.barChange Coeff G H f (n + 1) ≫
          (Rep.resFunctor f).map (Rep.barComplex.d Coeff G n ≫ g) := by rw [← Functor.map_comp]
    _ = SSGRoute.PTExt.barChange Coeff G H f (n + 1) ≫
          (Rep.resFunctor f).map ((Rep.barComplex Coeff G).d (n + 1) n ≫ g) := by
          rw [← Rep.barComplex.d_def (k := Coeff) (G := G)]
    _ = 0 := by rw [hg, Functor.map_zero, Limits.comp_zero]

lemma barChange_cocycle_phi {G H : Type} [Group G] [Group H] (f : H →* G)
    {A : Rep.{0, 0, 0} Coeff G} {B : Rep.{0, 0, 0} Coeff H} (φ : Rep.res f A ⟶ B) (n : ℕ)
    (g : (Rep.barComplex Coeff G).X n ⟶ A)
    (hg : (Rep.barComplex Coeff G).d (n + 1) n ≫ g = 0) :
    (Rep.barComplex Coeff H).d (n + 1) n ≫
      (SSGRoute.PTExt.barChange Coeff G H f n ≫ (Rep.resFunctor f).map g ≫ φ) = 0 := by
  have h2 := barChange_cocycle f n g hg
  calc (Rep.barComplex Coeff H).d (n + 1) n ≫
        (SSGRoute.PTExt.barChange Coeff G H f n ≫ (Rep.resFunctor f).map g ≫ φ)
      = ((Rep.barComplex Coeff H).d (n + 1) n ≫
          (SSGRoute.PTExt.barChange Coeff G H f n ≫ (Rep.resFunctor f).map g)) ≫ φ := by
          simp only [Category.assoc]
    _ = 0 ≫ φ := by rw [h2]
    _ = 0 := by rw [Limits.zero_comp]

/-! ## `extHMap` on `extMk` -/

set_option maxHeartbeats 1600000 in
theorem extHMap_extMk_apply {G H : Type} [Group G] [Group H] (f : H →* G)
    {A : Rep.{0, 0, 0} Coeff G} {B : Rep.{0, 0, 0} Coeff H} (φ : Rep.res f A ⟶ B) (n : ℕ)
    (g : (Rep.barComplex Coeff G).X n ⟶ A)
    (hg : (Rep.barComplex Coeff G).d (n + 1) n ≫ g = 0)
    (hg' : (Rep.barComplex Coeff H).d (n + 1) n ≫
        (SSGRoute.PTExt.barChange Coeff G H f n ≫ (Rep.resFunctor f).map g ≫ φ) = 0) :
    SSGRoute.PTExt.extHMap f φ ((Rep.barResolution Coeff G).extMk g (n + 1) rfl hg) =
      (Rep.barResolution Coeff H).extMk
        (SSGRoute.PTExt.barChange Coeff G H f n ≫ (Rep.resFunctor f).map g ≫ φ)
        (n + 1) rfl hg' := by
  have hmain := E0bGC.mapExtAddHom_extMk (C := Rep.{0, 0, 0} Coeff G)
    (D := Rep.{0, 0, 0} Coeff H) (F := Rep.resFunctor (k := Coeff) f)
    (X := SSGRoute.PTExt.unitRep G) (Y := A) (R := Rep.barResolution Coeff G)
    (n := n) (g := g) (hg := hg) (X' := SSGRoute.PTExt.unitRep H)
    (R' := Rep.barResolution Coeff H) (g' := SSGRoute.PTExt.unitRes f)
    (φ := SSGRoute.PTExt.barHom Coeff G H f)
    (hφ := SSGRoute.PTExt.barHom_augmentation Coeff G H f)
    (hg' := barChange_cocycle f n g hg)
  have hcomp : (Abelian.Ext.mk₀ (SSGRoute.PTExt.unitRes f)).comp
      (((Rep.barResolution Coeff G).extMk g (n + 1) rfl hg).mapExactFunctor
        (Rep.resFunctor (k := Coeff) f)) (zero_add n)
      = (Rep.barResolution Coeff H).extMk
          (SSGRoute.PTExt.barChange Coeff G H f n ≫ (Rep.resFunctor f).map g)
          (n + 1) rfl (barChange_cocycle f n g hg) := hmain
  have hstep : ((Rep.barResolution Coeff H).extMk
        (SSGRoute.PTExt.barChange Coeff G H f n ≫ (Rep.resFunctor f).map g)
        (n + 1) rfl (barChange_cocycle f n g hg)).comp (Abelian.Ext.mk₀ φ) (add_zero n)
      = (Rep.barResolution Coeff H).extMk
          ((SSGRoute.PTExt.barChange Coeff G H f n ≫ (Rep.resFunctor f).map g) ≫ φ)
          (n + 1) rfl _ :=
    ProjectiveResolution.extMk_comp_mk₀ (Rep.barResolution Coeff H) _ (n + 1) rfl _ φ
  unfold SSGRoute.PTExt.extHMap SSGRoute.PTExt.extRes
  rw [← Abelian.Ext.comp_assoc_of_third_deg_zero
    (Abelian.Ext.mk₀ (SSGRoute.PTExt.unitRes f))
    (((Rep.barResolution Coeff G).extMk g (n + 1) rfl hg).mapExactFunctor
      (Rep.resFunctor (k := Coeff) f)) (Abelian.Ext.mk₀ φ) (zero_add n)]
  rw [hcomp, hstep]
  refine Work.SSGRoute.E0bCore.extMk_congr (Rep.barResolution Coeff H) ?_ _ _
  simp only [Category.assoc]

/-! ## `Psi` is natural along the group-and-coefficient change -/

set_option maxHeartbeats 1600000 in
lemma Psi_natural_unit {G H : Type} [Group G] [Group H] (f : H →* G)
    {A : Rep.{0, 0, 0} Coeff G} {B : Rep.{0, 0, 0} Coeff H} (φ : Rep.res f A ⟶ B) (n : ℕ)
    (z : ((Bridge.barRes G).complex.linearYonedaObj Coeff A).homology n) :
    Bridge.Psi n H B (HomologicalComplex.homologyMap (lyBar f φ) n z) =
      SSGRoute.PTExt.extHMap f φ (Bridge.Psi n G A z) := by
  obtain ⟨c, hc⟩ := (ModuleCat.epi_iff_surjective
    (HomologicalComplex.homologyπ ((Bridge.barRes G).complex.linearYonedaObj Coeff A) n)).1
      inferInstance z
  rw [← hc]
  rw [Psi_homologyMap_homologypi (n := n) (G := H) (A := B) (K := _)
        (U := lyBar f φ) (c := c) (hc := by
          rw [lyBar_f_apply]
          exact barChange_cocycle_phi f φ n _ (iCycles_cocycle n G A c))]
  rw [Psi_apply_cycle n G A c]
  rw [extHMap_extMk_apply f φ n (Work.SSGRoute.E0bCore.cycHom (Bridge.barRes G) n c)
        (Work.SSGRoute.E0bCore.cycHom_cocycle (Bridge.barRes G) n c)
        (barChange_cocycle_phi f φ n _
          (Work.SSGRoute.E0bCore.cycHom_cocycle (Bridge.barRes G) n c))]
  refine Work.SSGRoute.E0bCore.extMk_congr (Bridge.barRes H) ?_ _ _
  show (lyBar f φ).f n (((Bridge.barRes G).complex.linearYonedaObj Coeff A).iCycles n c) =
    SSGRoute.PTExt.barChange Coeff G H f n ≫
      (Rep.resFunctor f).map (Work.SSGRoute.E0bCore.cycHom (Bridge.barRes G) n c) ≫ φ
  rw [lyBar_f_apply, ← Work.SSGRoute.E0bCore.iCycles_eq_cycHom (Bridge.barRes G) n c]

end

end Work.SSGRoute.E0bGroupCoeff

namespace Work.SSGRoute

open SSGRoute.PTExt

/-! ## The main theorem -/

/-- **Group cohomology is `Ext`-cohomology, naturally in the group and the coefficients (E0b, group-and-coefficient part only).**  For every degree `n`, group `G` and `A : Rep Coeff G` there is an additive isomorphism `Hⁿ(G, A) ≃+ extH A n = Extⁿ_G(ℤ, A)`, compatible with every change of group `f : H →* G` followed by a coefficient map `φ : Rep.res f A ⟶ B`:
`groupCohomology.map f φ n` corresponds to `extHMap f φ`.  (Only this naturality clause is asked for; the compatibility with connecting maps of short exact sequences is *not* part of this statement.  It is what the Sylow descent, E3Ω, E4Ω, E7cΩ and E9 need in order to move NK's and Commons' `groupCohomology` theorems — e.g. `Commons.RepresentationTheory.GroupCohomology.H2_inflation_injective_of_subsingleton_H1_general`, `NK.HassePrinciple.subsingleton_groupCohomology_one_ideleClassGroup_all` — into the `Ext` vocabulary of `PTDefs`.)

Route: Mathlib has `groupCohomologyIsoExt` and `ProjectiveResolution.extEquivCohomologyClass`; on disk, `Submission/Work/SSGRoute/projRes_homologyAddEquiv_extMk.lean` (sorry-free) already gives `(R.complex.linearYonedaObj k Y).homology n ≃+ Abelian.Ext X Y n` for a projective resolution `R` of `X`, and `Submission/Work/SSGRoute/E0bBarChange.lean` has the bar-resolution change-of-rings ingredients.  What remains (see `E0B_ROADMAP.md`) is `mapExtAddHom_extMk` (naturality of `extMk` along a functor/coefficient map) and the group-square naturality along `f : H →* G`, where `extHMap f φ` is `mapExactFunctor (Rep.resFunctor f)` followed by precomposition with `unitRes f` and postcomposition with `φ` (`Ext.mapExactFunctor_comp`, `Ext.mapExactFunctor_mk₀`). -/
theorem extH_groupCohomology_addEquiv :
    ∃ e : ∀ (n : ℕ) (G : Type) [Group G] (A : Rep SSGRoute.PTExt.Coeff G),
        groupCohomology A n ≃+ SSGRoute.PTExt.extH A n,
      ∀ (n : ℕ) (G H : Type) [Group G] [Group H] (f : H →* G) (A : Rep SSGRoute.PTExt.Coeff G)
        (B : Rep SSGRoute.PTExt.Coeff H) (φ : Rep.res f A ⟶ B) (y : groupCohomology A n),
        e n H B ((groupCohomology.map f φ n).hom y) = SSGRoute.PTExt.extHMap f φ (e n G A y) := by

  refine ⟨fun n G _ A => E0bGroupCoeff.eBridge n G A, ?_⟩
  intro n G H _ _ f A B φ y
  show E0bGroupCoeff.eBridge n H B ((groupCohomology.map f φ n).hom y) =
    SSGRoute.PTExt.extHMap f φ (E0bGroupCoeff.eBridge n G A y)
  rw [E0bGroupCoeff.eBridge_apply, E0bGroupCoeff.eBridge_apply]
  have h1 : HomologicalComplex.homologyMap (groupCohomology.inhomogeneousCochainsIso B).hom n
        ((groupCohomology.map f φ n).hom y)
      = HomologicalComplex.homologyMap (E0bGroupCoeff.lyBar f φ) n
          (HomologicalComplex.homologyMap (groupCohomology.inhomogeneousCochainsIso A).hom n y) := by
    have hcomp : HomologicalComplex.homologyMap (groupCohomology.cochainsMap f φ) n ≫
          HomologicalComplex.homologyMap (groupCohomology.inhomogeneousCochainsIso B).hom n
        = HomologicalComplex.homologyMap (groupCohomology.inhomogeneousCochainsIso A).hom n ≫
          HomologicalComplex.homologyMap (E0bGroupCoeff.lyBar f φ) n := by
      rw [← HomologicalComplex.homologyMap_comp, ← HomologicalComplex.homologyMap_comp,
        cochainsMap_inhomogeneousCochainsIso_comm Coeff G H f A B φ _
          (fun m g => E0bGroupCoeff.lyBar_f_apply f φ m g)]
    show (ModuleCat.Hom.hom (HomologicalComplex.homologyMap
            (groupCohomology.inhomogeneousCochainsIso B).hom n))
          (ModuleCat.Hom.hom (HomologicalComplex.homologyMap
            (groupCohomology.cochainsMap f φ) n) y)
        = (ModuleCat.Hom.hom (HomologicalComplex.homologyMap (E0bGroupCoeff.lyBar f φ) n))
          (ModuleCat.Hom.hom (HomologicalComplex.homologyMap
            (groupCohomology.inhomogeneousCochainsIso A).hom n) y)
    calc (ModuleCat.Hom.hom (HomologicalComplex.homologyMap
            (groupCohomology.inhomogeneousCochainsIso B).hom n))
          (ModuleCat.Hom.hom (HomologicalComplex.homologyMap
            (groupCohomology.cochainsMap f φ) n) y)
        = (ModuleCat.Hom.hom (HomologicalComplex.homologyMap
            (groupCohomology.cochainsMap f φ) n ≫
            HomologicalComplex.homologyMap (groupCohomology.inhomogeneousCochainsIso B).hom n)) y := by
            rw [ModuleCat.hom_comp]; rfl
      _ = (ModuleCat.Hom.hom (HomologicalComplex.homologyMap
            (groupCohomology.inhomogeneousCochainsIso A).hom n ≫
            HomologicalComplex.homologyMap (E0bGroupCoeff.lyBar f φ) n)) y := by
            rw [hcomp]
            rfl
      _ = (ModuleCat.Hom.hom (HomologicalComplex.homologyMap (E0bGroupCoeff.lyBar f φ) n))
          (ModuleCat.Hom.hom (HomologicalComplex.homologyMap
            (groupCohomology.inhomogeneousCochainsIso A).hom n) y) := by
            rw [ModuleCat.hom_comp]; rfl
  rw [h1]
  exact E0bGroupCoeff.Psi_natural_unit f φ n _

end Work.SSGRoute
