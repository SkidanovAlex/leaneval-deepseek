import Mathlib
import Submission.Work.SSGRoute.extH_groupCohomology_addEquiv
import Submission.Work.SSGRoute.extHRestrict_comp_mk0
import Submission.NK.GlobalCFTdeep.HasseNormTheorem
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The Hasse–Brauer–Noether principle in the `Ext` core

`Work.SSGRoute.hbn_ext_units` is the `Ext`-vocabulary form of the relative
Hasse–Brauer–Noether theorem `NK.GlobalCFTdeep.hbnUnits` (Milne, *CFT*, VII.7.1): a class
`a ∈ H²(Gal(L/k), Lˣ) = extH (unitsK k L) 2` whose localisation at every place of `L`
vanishes is zero.

The transport is along the E0b comparison `Hⁿ(G, A) ≃+ extH A n` (`E0bGroupCoeff.eBridge`),
natural under every change of group `f : H →* G` followed by a coefficient map
`φ : Rep.res f A ⟶ B`.  The naturality square for `eBridge` is proved below
(`hbnAux_eBridge_natural`) from the `extMk`-naturality lemma `mapExtAddHom_extMk`
(the one gap in Mathlib's `Ext` API; see `E0B_ROADMAP.md`) rather than from the packaged
existential `extH_groupCohomology_addEquiv`, so that the present file can be verified
independently of that node's own state.
-/

open CategoryTheory
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

namespace Work.SSGRoute

open SSGRoute.PTExt
open scoped Classical

noncomputable section

/-! ## The E0b group-change naturality, re-derived -/

/-- `extHMap` commutes with `extMk` along the bar resolutions.  (The `F`-resolution-lift input
`mapExtAddHom_extMk` is the single gap in Mathlib's `Ext` API.) -/
theorem hbnAux_extHMap_extMk_apply {G H : Type} [Group G] [Group H] (f : H →* G)
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
    (hg' := E0bGroupCoeff.barChange_cocycle f n g hg)
  have hcomp : (Abelian.Ext.mk₀ (SSGRoute.PTExt.unitRes f)).comp
      (((Rep.barResolution Coeff G).extMk g (n + 1) rfl hg).mapExactFunctor
        (Rep.resFunctor (k := Coeff) f)) (zero_add n)
      = (Rep.barResolution Coeff H).extMk
          (SSGRoute.PTExt.barChange Coeff G H f n ≫ (Rep.resFunctor f).map g)
          (n + 1) rfl (E0bGroupCoeff.barChange_cocycle f n g hg) := hmain
  have hstep : ((Rep.barResolution Coeff H).extMk
        (SSGRoute.PTExt.barChange Coeff G H f n ≫ (Rep.resFunctor f).map g)
        (n + 1) rfl (E0bGroupCoeff.barChange_cocycle f n g hg)).comp
          (Abelian.Ext.mk₀ φ) (add_zero n)
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
  refine E0bCore.extMk_congr (Rep.barResolution Coeff H) ?_ _ _
  simp only [Category.assoc]

/-- `Bridge.Psi` is natural along the group-and-coefficient change. -/
theorem hbnAux_Psi_natural_unit {G H : Type} [Group G] [Group H] (f : H →* G)
    {A : Rep.{0, 0, 0} Coeff G} {B : Rep.{0, 0, 0} Coeff H} (φ : Rep.res f A ⟶ B) (n : ℕ)
    (z : ((Bridge.barRes G).complex.linearYonedaObj Coeff A).homology n) :
    Bridge.Psi n H B (HomologicalComplex.homologyMap (E0bGroupCoeff.lyBar f φ) n z) =
      SSGRoute.PTExt.extHMap f φ (Bridge.Psi n G A z) := by
  obtain ⟨c, hc⟩ := (ModuleCat.epi_iff_surjective
    (HomologicalComplex.homologyπ ((Bridge.barRes G).complex.linearYonedaObj Coeff A) n)).1
      inferInstance z
  rw [← hc]
  rw [E0bGroupCoeff.Psi_homologyMap_homologypi (n := n) (G := H) (A := B) (K := _)
        (U := E0bGroupCoeff.lyBar f φ) (c := c) (hc := by
          rw [E0bGroupCoeff.lyBar_f_apply]
          exact E0bGroupCoeff.barChange_cocycle_phi f φ n _
            (E0bGroupCoeff.iCycles_cocycle n G A c))]
  rw [E0bGroupCoeff.Psi_apply_cycle n G A c]
  rw [hbnAux_extHMap_extMk_apply f φ n (E0bCore.cycHom (Bridge.barRes G) n c)
        (E0bCore.cycHom_cocycle (Bridge.barRes G) n c)
        (E0bGroupCoeff.barChange_cocycle_phi f φ n _
          (E0bCore.cycHom_cocycle (Bridge.barRes G) n c))]
  refine E0bCore.extMk_congr (Bridge.barRes H) ?_ _ _
  show (E0bGroupCoeff.lyBar f φ).f n
      (((Bridge.barRes G).complex.linearYonedaObj Coeff A).iCycles n c) =
    SSGRoute.PTExt.barChange Coeff G H f n ≫
      (Rep.resFunctor f).map (E0bCore.cycHom (Bridge.barRes G) n c) ≫ φ
  rw [E0bGroupCoeff.lyBar_f_apply, ← E0bCore.iCycles_eq_cycHom (Bridge.barRes G) n c]

/-- **E0b naturality for `eBridge`**: `Hⁿ(G, A) ≃+ extH A n` is compatible with every change of
group `f : H →* G` followed by a coefficient map `φ : Rep.res f A ⟶ B`. -/
theorem hbnAux_eBridge_natural {G H : Type} [Group G] [Group H] (f : H →* G)
    {A : Rep.{0, 0, 0} Coeff G} {B : Rep.{0, 0, 0} Coeff H} (φ : Rep.res f A ⟶ B) (n : ℕ)
    (y : groupCohomology A n) :
    E0bGroupCoeff.eBridge n H B ((groupCohomology.map f φ n).hom y) =
      SSGRoute.PTExt.extHMap f φ (E0bGroupCoeff.eBridge n G A y) := by
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
  exact hbnAux_Psi_natural_unit f φ n _


/-! ## NK's localisation `locUnits` is a single `groupCohomology.map` -/

theorem hbnAux_map_f_comp_id {k' : Type} [CommRing k'] {G H : Type} [Group G] [Group H]
    (f : G →* H) {A : Rep k' H} {B C : Rep k' G} (φ : Rep.res f A ⟶ B) (ψ : B ⟶ C) (n : ℕ) :
    groupCohomology.map f (φ ≫ ψ) n =
      groupCohomology.map f φ n ≫ groupCohomology.map (MonoidHom.id G) ψ n := by
  rw [← groupCohomology.map_comp f (MonoidHom.id G) φ ψ n]
  refine groupCohomology.map_congr (MonoidHom.comp_id f).symm ?_ n
  rfl

theorem hbnAux_map_id_comp_apply {k' : Type} [CommRing k'] {G H : Type} [Group G] [Group H]
    (f : G →* H) {A : Rep k' H} {C : Rep k' G} (X : Rep.res f A ⟶ C) (n : ℕ) :
    groupCohomology.map f (𝟙 (Rep.res f A)) n ≫ groupCohomology.map (MonoidHom.id G) X n =
      groupCohomology.map f X n := by
  rw [← hbnAux_map_f_comp_id f (𝟙 (Rep.res f A)) X n]
  simp

/-- NK's localisation at a place is a single `groupCohomology.map`: restriction to the
decomposition group followed by the coefficient map `Lˣ → L_wˣ`. -/
theorem hbnAux_locUnits_eq_map {k L : Type} [Field k] [NumberField k] [Field L] [NumberField L]
    [Algebra k L] [FiniteDimensional k L] [IsGalois k L] (w : NK.GlobalCFT.Place L) :
    NK.HassePrinciple.locUnits k L w =
      groupCohomology.map (MulAction.stabilizer (L ≃ₐ[k] L) w).subtype
        (NK.HassePrinciple.unitsToLocalUnits k L w) 2 := by
  rw [NK.HassePrinciple.locUnits]
  simp only [groupCohomology.resNatTrans_app]
  exact hbnAux_map_id_comp_apply _ _ 2

/-! ## The Hasse principle in the `Ext` core -/


theorem hbn_ext_units (k L : Type) [Field k] [NumberField k] [Field L] [NumberField L]
    [Algebra k L] [FiniteDimensional k L] [IsGalois k L] :
    ∀ a : SSGRoute.PTExt.extH (SSGRoute.PTExt.unitsK k L) 2,
      (∀ w : NK.GlobalCFT.Place L,
        (SSGRoute.PTExt.extHRestrict (MulAction.stabilizer (L ≃ₐ[k] L) w) a).comp
          (CategoryTheory.Abelian.Ext.mk₀ (NK.HassePrinciple.unitsToLocalUnits k L w))
          (add_zero 2) = 0) → a = 0 := by
  intro a ha
  have hloc : ∀ w : NK.GlobalCFT.Place L,
      (NK.HassePrinciple.locUnits k L w).hom
        ((E0bGroupCoeff.eBridge 2 (L ≃ₐ[k] L) (unitsK k L)).symm a) = 0 := by
    intro w
    have hn := hbnAux_eBridge_natural (G := L ≃ₐ[k] L)
      (H := MulAction.stabilizer (L ≃ₐ[k] L) w)
      (MulAction.stabilizer (L ≃ₐ[k] L) w).subtype (A := unitsK k L)
      (B := NK.HassePrinciple.localUnitsRep k L w)
      (NK.HassePrinciple.unitsToLocalUnits k L w) 2
      ((E0bGroupCoeff.eBridge 2 (L ≃ₐ[k] L) (unitsK k L)).symm a)
    rw [AddEquiv.apply_symm_apply] at hn
    have hzero : extHMap (MulAction.stabilizer (L ≃ₐ[k] L) w).subtype
        (NK.HassePrinciple.unitsToLocalUnits k L w) a = 0 := by
      rw [← extHRestrict_comp_mk0 (MulAction.stabilizer (L ≃ₐ[k] L) w) a
        (NK.HassePrinciple.unitsToLocalUnits k L w)]
      exact ha w
    rw [hzero] at hn
    rw [hbnAux_locUnits_eq_map (k := k) (L := L) w]
    refine (E0bGroupCoeff.eBridge 2 (MulAction.stabilizer (L ≃ₐ[k] L) w)
      (NK.HassePrinciple.localUnitsRep k L w)).injective ?_
    rw [hn, map_zero]
  have hb0 := NK.GlobalCFTdeep.hbnUnits (F := k) (E := L)
    ((E0bGroupCoeff.eBridge 2 (L ≃ₐ[k] L) (unitsK k L)).symm a) hloc
  calc a = E0bGroupCoeff.eBridge 2 (L ≃ₐ[k] L) (unitsK k L)
        ((E0bGroupCoeff.eBridge 2 (L ≃ₐ[k] L) (unitsK k L)).symm a) :=
        (AddEquiv.apply_symm_apply (E0bGroupCoeff.eBridge 2 (L ≃ₐ[k] L) (unitsK k L)) a).symm
    _ = 0 := by rw [hb0, map_zero]

end

end Work.SSGRoute
