import Mathlib
import Submission.Work.SSGRoute.Phi0Aux
import Submission.Work.SSGRoute.extH_groupCohomology_addEquiv
import Submission.Work.SSGRoute.mapExtAddHom_extMk_univ
import Submission.Work.SSGRoute.bridgeE_map_coeff
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Naturality of the bridge `bridgeE` (E0b), group-and-coefficient version

`Work.SSGRoute.bridgeE_map` is the clause `Hⁿ(G,A) ≃+ Extⁿ_G(ℤ,A)` natural in a group change
`f : H →* G` followed by a coefficient map `φ : Rep.res f A ⟶ B`.

The only non-elementary input is `Work.SSGRoute.barChange_extMk` (the group-change naturality of
`ProjectiveResolution.extMk` along `Rep.resFunctor f`, at the bar resolutions); everything else is
the standard cube chase: naturality of `inhomogeneousCochainsIso`, then naturality of `Bridge.Psi`.
-/

namespace Work.SSGRoute

open CategoryTheory SSGRoute.PTExt
open scoped Classical

set_option backward.isDefEq.respectTransparency false

noncomputable section

/-- **`extHMap` on `extMk`** — the group-change version, obtained from `barChange_extMk`. -/
theorem extHMap_extMk_apply_bar {G H : Type} [Group G] [Group H] (f : H →* G)
    {A : Rep.{0, 0, 0} Coeff G} {B : Rep.{0, 0, 0} Coeff H} (φ : Rep.res f A ⟶ B) (n : ℕ)
    (g : (Rep.barComplex Coeff G).X n ⟶ A)
    (hg : (Rep.barComplex Coeff G).d (n + 1) n ≫ g = 0)
    (hg' : (Rep.barComplex Coeff H).d (n + 1) n ≫
        (SSGRoute.PTExt.barChange Coeff G H f n ≫ (Rep.resFunctor f).map g ≫ φ) = 0) :
    SSGRoute.PTExt.extHMap f φ ((Rep.barResolution Coeff G).extMk g (n + 1) rfl hg) =
      (Rep.barResolution Coeff H).extMk
        (SSGRoute.PTExt.barChange Coeff G H f n ≫ (Rep.resFunctor f).map g ≫ φ)
        (n + 1) rfl hg' := by
  have hmain := mapExtAddHom_extMk_univ (F := Rep.resFunctor (k := Coeff) f)
      (R := Rep.barResolution Coeff G) (g := g) (hg := hg)
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
  refine Work.SSGRoute.E0bCore.extMk_congr (Rep.barResolution Coeff H) ?_ _ _
  rw [Category.assoc]

set_option maxHeartbeats 1600000 in
/-- **`Bridge.Psi` is natural in the group and the coefficients.** -/
lemma Psi_natural_unit_bar {G H : Type} [Group G] [Group H] (f : H →* G)
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
  rw [extHMap_extMk_apply_bar f φ n (Work.SSGRoute.E0bCore.cycHom (Bridge.barRes G) n c)
        (Work.SSGRoute.E0bCore.cycHom_cocycle (Bridge.barRes G) n c)
        (E0bGroupCoeff.barChange_cocycle_phi f φ n _
          (Work.SSGRoute.E0bCore.cycHom_cocycle (Bridge.barRes G) n c))]
  refine Work.SSGRoute.E0bCore.extMk_congr (Bridge.barRes H) ?_ _ _
  show (E0bGroupCoeff.lyBar f φ).f n
        (((Bridge.barRes G).complex.linearYonedaObj Coeff A).iCycles n c) =
    SSGRoute.PTExt.barChange Coeff G H f n ≫
      (Rep.resFunctor f).map (Work.SSGRoute.E0bCore.cycHom (Bridge.barRes G) n c) ≫ φ
  rw [E0bGroupCoeff.lyBar_f_apply, ← Work.SSGRoute.E0bCore.iCycles_eq_cycHom (Bridge.barRes G) n c]

/-- **`thetaHom` is natural in the group and the coefficients.** -/
lemma thetaHom_natural_bar {G H : Type} [Group G] [Group H] (f : H →* G)
    {A : Rep.{0, 0, 0} Coeff G} {B : Rep.{0, 0, 0} Coeff H} (φ : Rep.res f A ⟶ B) (n : ℕ)
    (x : groupCohomology A n) :
    thetaHom H B n ((groupCohomology.map f φ n).hom x) =
      HomologicalComplex.homologyMap (E0bGroupCoeff.lyBar f φ) n (thetaHom G A n x) := by
  have h1 : HomologicalComplex.homologyMap (groupCohomology.inhomogeneousCochainsIso B).hom n
        ((groupCohomology.map f φ n).hom x)
      = HomologicalComplex.homologyMap (E0bGroupCoeff.lyBar f φ) n
          (HomologicalComplex.homologyMap (groupCohomology.inhomogeneousCochainsIso A).hom n x) := by
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
            (groupCohomology.cochainsMap f φ) n) x)
        = (ModuleCat.Hom.hom (HomologicalComplex.homologyMap (E0bGroupCoeff.lyBar f φ) n))
          (ModuleCat.Hom.hom (HomologicalComplex.homologyMap
            (groupCohomology.inhomogeneousCochainsIso A).hom n) x)
    calc (ModuleCat.Hom.hom (HomologicalComplex.homologyMap
            (groupCohomology.inhomogeneousCochainsIso B).hom n))
          (ModuleCat.Hom.hom (HomologicalComplex.homologyMap
            (groupCohomology.cochainsMap f φ) n) x)
        = (ModuleCat.Hom.hom (HomologicalComplex.homologyMap
            (groupCohomology.cochainsMap f φ) n ≫
            HomologicalComplex.homologyMap (groupCohomology.inhomogeneousCochainsIso B).hom n)) x := by
            rw [ModuleCat.hom_comp]; rfl
      _ = (ModuleCat.Hom.hom (HomologicalComplex.homologyMap
            (groupCohomology.inhomogeneousCochainsIso A).hom n ≫
            HomologicalComplex.homologyMap (E0bGroupCoeff.lyBar f φ) n)) x := by
            rw [hcomp]
            rfl
      _ = (ModuleCat.Hom.hom (HomologicalComplex.homologyMap (E0bGroupCoeff.lyBar f φ) n))
          (ModuleCat.Hom.hom (HomologicalComplex.homologyMap
            (groupCohomology.inhomogeneousCochainsIso A).hom n) x) := by
            rw [ModuleCat.hom_comp]; rfl
  show (HomologicalComplex.homologyMap (groupCohomology.inhomogeneousCochainsIso B).hom n)
        ((groupCohomology.map f φ n).hom x)
      = HomologicalComplex.homologyMap (E0bGroupCoeff.lyBar f φ) n
        (HomologicalComplex.homologyMap (groupCohomology.inhomogeneousCochainsIso A).hom n x)
  exact h1

/-- **Naturality of the bridge `bridgeE`.** -/
theorem bridgeE_map {G H : Type} [Group G] [Group H] (f : H →* G)
    (A : Rep.{0, 0, 0} SSGRoute.PTExt.Coeff G) (B : Rep.{0, 0, 0} SSGRoute.PTExt.Coeff H)
    (φ : Quiver.Hom (Rep.res f A) B) (n : ℕ) (x : groupCohomology A n) :
    Work.SSGRoute.bridgeE H B n ((groupCohomology.map f φ n).hom x) =
      SSGRoute.PTExt.extHMap f φ (Work.SSGRoute.bridgeE G A n x) := by
  show Bridge.Psi n H B (thetaHom H B n ((groupCohomology.map f φ n).hom x)) =
    SSGRoute.PTExt.extHMap f φ (Bridge.Psi n G A (thetaHom G A n x))
  rw [thetaHom_natural_bar f φ n x]
  exact Psi_natural_unit_bar f φ n (thetaHom G A n x)

end

end Work.SSGRoute
