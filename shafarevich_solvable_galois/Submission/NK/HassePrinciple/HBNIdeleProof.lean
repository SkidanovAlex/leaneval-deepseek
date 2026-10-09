/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The Hasse principle for the idèles: `NK.HassePrinciple.hbnIdele`

This module assembles the proof of `NK.HassePrinciple.HBNIdele K L`: the localisation
`H²(Gal(L/K), 𝕀_L) ⟶ ∏_w H²(Γ_w, L_wˣ)` is injective.

The argument runs on the filtered system of the finite `Gal(L/K)`-stable sets `S` of places
(`NK.HassePrinciple.levelRep K L S = 𝕀_L^S`):

* every class of `H²(Γ, 𝕀_L)` comes from a level (`exists_level_of_h2`);
* on a level, the localisation at a place `w` factors through the projection onto the summand of
  the decomposition `𝕀_L^S = A_S × U_S` (`A_S = ∏_{v ∈ S} L_vˣ`, `U_S = ∏_{v ∉ S} 𝒪_vˣ`)
  corresponding to the orbit of `w`: for `w ∈ S` through `A_S` (`ideleLoc_level_comp`), and for
  `w ∉ S` through `U_S` (`ideleLoc_level_comp_U`, using the injectivity of `H²(Γ_w, 𝒪_wˣ) →
  H²(Γ_w, L_wˣ)` of `localUnits_h2_injective`);
* together with Shapiro's isomorphism and its splitting (`orbitCoindMapA_split`,
  `orbitCoindMapU_split`) this shows that every orbit component of both projections of a level class
  vanishes, so that the orbit decompositions (`supportedLift_split`, `outsideUnitsLift_split`)
  together with `piRep_injective` give `π_A a_S = 0` (`level_proj_zero`) and `π_U a_S = 0`
  (`level_outside_zero`);
* finally `π_A ≫ i_A + π_U ≫ i_U = 𝟙` (`level_decomposition`) and the additivity of `h2map`
  (`h2map_add`) exhibit `a_S` as the sum of the two projections, so `a_S = 0` -- and hence so is the
  original class.
-/

import Mathlib
import Submission.NK.HassePrinciple.IdeleLevelGlue
import Submission.NK.HassePrinciple.orbitCoindMapA_split
import Submission.NK.HassePrinciple.supportedLift_split
import Submission.NK.HassePrinciple.exists_level_of_h2
import Submission.NK.HassePrinciple.orbitCoindMapU_split
import Submission.NK.HassePrinciple.outsideUnitsLift_split
import Submission.NK.HassePrinciple.localUnits_h2_injective
import Submission.NK.RepresentationTheory.GroupCohomology.res_counit_eq_coindIso
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace NK.HassePrinciple

open CategoryTheory Representation
open NK.GlobalCFT
open scoped NumberField

noncomputable section

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L]

attribute [local instance 10000] Rep.hV2 Rep.hV1

/-! ## The map induced by a morphism of representations on `H²` -/

/-- The map induced by a morphism of `Gal(L/K)`-representations on `H²`. -/
def h2map {M N : Rep.{0, 0, 0} CoeffInt.{0} (L ≃ₐ[K] L)} (φ : M ⟶ N) :
    groupCohomology M 2 ⟶ groupCohomology N 2 :=
  (groupCohomology.functor CoeffInt.{0} (L ≃ₐ[K] L) 2).map φ

@[simp]
theorem h2map_id (M : Rep.{0, 0, 0} CoeffInt.{0} (L ≃ₐ[K] L)) :
    h2map (𝟙 M) = 𝟙 (groupCohomology M 2) :=
  CategoryTheory.Functor.map_id _ _

theorem h2map_comp {M N P : Rep.{0, 0, 0} CoeffInt.{0} (L ≃ₐ[K] L)} (φ : M ⟶ N) (ψ : N ⟶ P) :
    h2map (φ ≫ ψ) = h2map φ ≫ h2map ψ :=
  CategoryTheory.Functor.map_comp _ _ _

/-- Composition of two functorial maps on `H²`, in the form in which it is used when the maps are
applied to a class. -/
theorem h2map_apply_comp {M N P : Rep.{0, 0, 0} CoeffInt.{0} (L ≃ₐ[K] L)} (φ : M ⟶ N)
    (ψ : N ⟶ P) (y : groupCohomology M 2) :
    ((h2map ψ).hom) (((h2map φ).hom) y) = ((h2map (φ ≫ ψ)).hom) y := by
  rw [h2map, h2map, h2map, Functor.map_comp, ModuleCat.comp_apply]
  rfl

/-! ## The functoriality of the localisation -/

/-- Naturality of the restriction map, in the form in which it is used by the definitions of the
localisation. -/
theorem resNatTrans_naturality_map {M N : Rep.{0, 0, 0} CoeffInt.{0} (L ≃ₐ[K] L)} (w : Place L)
    (φ : M ⟶ N) :
    groupCohomology.map (MonoidHom.id (L ≃ₐ[K] L)) φ 2 ≫
        groupCohomology.map (MulAction.stabilizer (L ≃ₐ[K] L) w).subtype
          (𝟙 (Rep.res (MulAction.stabilizer (L ≃ₐ[K] L) w).subtype N)) 2
      = groupCohomology.map (MulAction.stabilizer (L ≃ₐ[K] L) w).subtype
          (𝟙 (Rep.res (MulAction.stabilizer (L ≃ₐ[K] L) w).subtype M)) 2 ≫
        groupCohomology.map (MonoidHom.id (MulAction.stabilizer (L ≃ₐ[K] L) w))
          (Rep.resMap (MulAction.stabilizer (L ≃ₐ[K] L) w).subtype φ) 2 := by
  have h := (groupCohomology.resNatTrans CoeffInt.{0} (G := MulAction.stabilizer (L ≃ₐ[K] L) w)
      (H := L ≃ₐ[K] L) (MulAction.stabilizer (L ≃ₐ[K] L) w).subtype 2).naturality φ
  simpa only [groupCohomology.resNatTrans_app, groupCohomology.functor_map, Functor.comp_map,
    Functor.comp_obj, groupCohomology.functor_obj, Rep.resMap] using h

/-! ## The localisation at a place, on a level -/

/-- **The localisation at a place of a level, computed on the coinduced model** (morphism form).

For `w ∈ S`, the composite of the inclusion `𝕀_L^S ⟶ 𝕀_L` with the localisation `ideleLoc K L w` is
the composite of the projection of the level onto `A_S = ∏_{v ∈ S} L_vˣ`, the projection onto the
orbit component `A_O` (`O = Γ·w`), the Shapiro comparison map `A_O ⟶ Coind_{Γ_w}^Γ L_wˣ` and
Shapiro's isomorphism. -/
theorem ideleLoc_level_comp (S : GStableSet K L) (w : Place L) (hw : w ∈ S.carrier) :
    h2map (levelIncl K L S) ≫ ideleLoc K L w
      = h2map (levelToSupportedHom K L S) ≫
        h2map (projSupportedHom K L S (orbitStable K L w)) ≫
        h2map (orbitCoindMapA K L w) ≫
        (groupCohomology.coindIso (k := CoeffInt.{0})
          (S := MulAction.stabilizer (L ≃ₐ[K] L) w) (localUnitsRep K L w) 2).hom := by
  set f := (MulAction.stabilizer (L ≃ₐ[K] L) w).subtype with hf
  have h1 : h2map (levelIncl K L S) ≫ groupCohomology.map f (𝟙 (Rep.res f (ideleRep K L))) 2
      = groupCohomology.map f (𝟙 (Rep.res f (levelRep K L S))) 2 ≫
        groupCohomology.map (MonoidHom.id (MulAction.stabilizer (L ≃ₐ[K] L) w))
          (Rep.resMap f (levelIncl K L S)) 2 :=
    (groupCohomology.resNatTrans CoeffInt (f := f) 2).naturality (levelIncl K L S)
  have h2 : Rep.resMap f (levelIncl K L S) ≫ ideleToLocalUnits K L w
      = (Rep.resMap f (levelToSupportedHom K L S) ≫
          Rep.resMap f (projSupportedHom K L S (orbitStable K L w)) ≫
          orbitCoordA K L w) := res_levelIncl_comp_A S w hw
  have h3 : groupCohomology.map f (𝟙 (Rep.res f (levelRep K L S))) 2 ≫
        groupCohomology.map (MonoidHom.id (MulAction.stabilizer (L ≃ₐ[K] L) w))
          (Rep.resMap f (levelToSupportedHom K L S)) 2
      = h2map (levelToSupportedHom K L S) ≫
        groupCohomology.map f (𝟙 (Rep.res f (supportedRep K L S))) 2 :=
    ((groupCohomology.resNatTrans CoeffInt (f := f) 2).naturality
      (levelToSupportedHom K L S)).symm
  have h4 : groupCohomology.map f (𝟙 (Rep.res f (supportedRep K L S))) 2 ≫
        groupCohomology.map (MonoidHom.id (MulAction.stabilizer (L ≃ₐ[K] L) w))
          (Rep.resMap f (projSupportedHom K L S (orbitStable K L w))) 2
      = h2map (projSupportedHom K L S (orbitStable K L w)) ≫
        groupCohomology.map f
          (𝟙 (Rep.res f (supportedRep K L (orbitStable K L w)))) 2 :=
    ((groupCohomology.resNatTrans CoeffInt (f := f) 2).naturality
      (projSupportedHom K L S (orbitStable K L w))).symm
  have h5 : groupCohomology.map f
        (𝟙 (Rep.res f (supportedRep K L (orbitStable K L w)))) 2 ≫
        groupCohomology.map (MonoidHom.id (MulAction.stabilizer (L ≃ₐ[K] L) w))
          (orbitCoordA K L w) 2
      = h2map (orbitCoindMapA K L w) ≫
        (groupCohomology.coindIso (k := CoeffInt.{0})
          (S := MulAction.stabilizer (L ≃ₐ[K] L) w) (localUnitsRep K L w) 2).hom := by
    have hnatOC : h2map (orbitCoindMapA K L w) ≫
          (groupCohomology.resNatTrans CoeffInt (f := f) 2).app
            (Rep.coind (MulAction.stabilizer (L ≃ₐ[K] L) w).subtype (localUnitsRep K L w))
        = (groupCohomology.resNatTrans CoeffInt (f := f) 2).app
            (supportedRep K L (orbitStable K L w)) ≫
          groupCohomology.map (MonoidHom.id (MulAction.stabilizer (L ≃ₐ[K] L) w))
            (Rep.resMap f (orbitCoindMapA K L w)) 2 := by
      simpa only [h2map, groupCohomology.functor_map, Functor.comp_map, Functor.comp_obj,
        groupCohomology.functor_obj, Rep.resMap] using
        (groupCohomology.resNatTrans CoeffInt (f := f) 2).naturality (orbitCoindMapA K L w)
    rw [← NK.RepresentationTheory.GroupCohomology.res_counit_eq_coindIso
      (MulAction.stabilizer (L ≃ₐ[K] L) w) (localUnitsRep K L w) 2]
    rw [← Category.assoc]
    rw [hnatOC]
    rw [Category.assoc]
    rw [← groupCohomology.map_id_comp (Rep.resMap f (orbitCoindMapA K L w))
      ((Rep.resCoindAdjunction CoeffInt.{0}
        (MulAction.stabilizer (L ≃ₐ[K] L) w).subtype).counit.app
        (localUnitsRep K L w)) 2]
    have htri : Rep.resMap (MulAction.stabilizer (L ≃ₐ[K] L) w).subtype
          (orbitCoindMapA K L w) ≫
          (Rep.resCoindAdjunction CoeffInt.{0}
            (MulAction.stabilizer (L ≃ₐ[K] L) w).subtype).counit.app (localUnitsRep K L w)
        = orbitCoordA K L w :=
      res_coindToHom_counit w (supportedRep K L (orbitStable K L w)) (localUnitsRep K L w)
        (orbitCoordA K L w)
    rw [htri]
    simp only [groupCohomology.resNatTrans_app]
  calc h2map (levelIncl K L S) ≫ ideleLoc K L w
      = (h2map (levelIncl K L S) ≫
          groupCohomology.map f (𝟙 (Rep.res f (ideleRep K L))) 2) ≫
          groupCohomology.map (MonoidHom.id (MulAction.stabilizer (L ≃ₐ[K] L) w))
            (ideleToLocalUnits K L w) 2 := by
        rw [show ideleLoc K L w = groupCohomology.map f (𝟙 (Rep.res f (ideleRep K L))) 2 ≫
          groupCohomology.map (MonoidHom.id (MulAction.stabilizer (L ≃ₐ[K] L) w))
            (ideleToLocalUnits K L w) 2 from rfl, ← Category.assoc]
    _ = (groupCohomology.map f (𝟙 (Rep.res f (levelRep K L S))) 2 ≫
          groupCohomology.map (MonoidHom.id (MulAction.stabilizer (L ≃ₐ[K] L) w))
            (Rep.resMap f (levelIncl K L S)) 2) ≫
          groupCohomology.map (MonoidHom.id (MulAction.stabilizer (L ≃ₐ[K] L) w))
            (ideleToLocalUnits K L w) 2 := by
        rw [h1]
    _ = groupCohomology.map f (𝟙 (Rep.res f (levelRep K L S))) 2 ≫
          groupCohomology.map (MonoidHom.id (MulAction.stabilizer (L ≃ₐ[K] L) w))
            (Rep.resMap f (levelIncl K L S) ≫ ideleToLocalUnits K L w) 2 := by
        rw [Category.assoc, ← groupCohomology.map_id_comp (Rep.resMap f (levelIncl K L S))
          (ideleToLocalUnits K L w) 2]
    _ = groupCohomology.map f (𝟙 (Rep.res f (levelRep K L S))) 2 ≫
          groupCohomology.map (MonoidHom.id (MulAction.stabilizer (L ≃ₐ[K] L) w))
            (Rep.resMap f (levelToSupportedHom K L S) ≫
              Rep.resMap f (projSupportedHom K L S (orbitStable K L w)) ≫
              orbitCoordA K L w) 2 := by
        rw [h2]
    _ = (groupCohomology.map f (𝟙 (Rep.res f (levelRep K L S))) 2 ≫
          groupCohomology.map (MonoidHom.id (MulAction.stabilizer (L ≃ₐ[K] L) w))
            (Rep.resMap f (levelToSupportedHom K L S)) 2) ≫
          (groupCohomology.map (MonoidHom.id (MulAction.stabilizer (L ≃ₐ[K] L) w))
            (Rep.resMap f (projSupportedHom K L S (orbitStable K L w))) 2 ≫
          groupCohomology.map (MonoidHom.id (MulAction.stabilizer (L ≃ₐ[K] L) w))
            (orbitCoordA K L w) 2) := by
        rw [groupCohomology.map_id_comp (Rep.resMap f (levelToSupportedHom K L S))
            (Rep.resMap f (projSupportedHom K L S (orbitStable K L w)) ≫
              orbitCoordA K L w) 2,
          groupCohomology.map_id_comp (Rep.resMap f (projSupportedHom K L S (orbitStable K L w)))
            (orbitCoordA K L w) 2,
          ← Category.assoc]
    _ = (h2map (levelToSupportedHom K L S) ≫
          groupCohomology.map f (𝟙 (Rep.res f (supportedRep K L S))) 2) ≫
          (groupCohomology.map (MonoidHom.id (MulAction.stabilizer (L ≃ₐ[K] L) w))
            (Rep.resMap f (projSupportedHom K L S (orbitStable K L w))) 2 ≫
          groupCohomology.map (MonoidHom.id (MulAction.stabilizer (L ≃ₐ[K] L) w))
            (orbitCoordA K L w) 2) := by
        rw [h3]
    _ = h2map (levelToSupportedHom K L S) ≫
          ((groupCohomology.map f (𝟙 (Rep.res f (supportedRep K L S))) 2 ≫
            groupCohomology.map (MonoidHom.id (MulAction.stabilizer (L ≃ₐ[K] L) w))
              (Rep.resMap f (projSupportedHom K L S (orbitStable K L w))) 2) ≫
            groupCohomology.map (MonoidHom.id (MulAction.stabilizer (L ≃ₐ[K] L) w))
              (orbitCoordA K L w) 2) := by
        simp only [Category.assoc]
    _ = h2map (levelToSupportedHom K L S) ≫
          ((h2map (projSupportedHom K L S (orbitStable K L w)) ≫
            groupCohomology.map f
              (𝟙 (Rep.res f (supportedRep K L (orbitStable K L w)))) 2) ≫
            groupCohomology.map (MonoidHom.id (MulAction.stabilizer (L ≃ₐ[K] L) w))
              (orbitCoordA K L w) 2) := by
        rw [h4]
    _ = h2map (levelToSupportedHom K L S) ≫
          (h2map (projSupportedHom K L S (orbitStable K L w)) ≫
          (groupCohomology.map f
              (𝟙 (Rep.res f (supportedRep K L (orbitStable K L w)))) 2 ≫
            groupCohomology.map (MonoidHom.id (MulAction.stabilizer (L ≃ₐ[K] L) w))
              (orbitCoordA K L w) 2)) := by
        rw [Category.assoc]
    _ = h2map (levelToSupportedHom K L S) ≫
          (h2map (projSupportedHom K L S (orbitStable K L w)) ≫
          (h2map (orbitCoindMapA K L w) ≫
            (groupCohomology.coindIso (k := CoeffInt.{0})
              (S := MulAction.stabilizer (L ≃ₐ[K] L) w) (localUnitsRep K L w) 2).hom)) := by
        rw [h5]

theorem ideleLoc_level_eq_A (S : GStableSet K L) (w : Place L) (hw : w ∈ S.carrier)
    (a_S : groupCohomology (levelRep K L S) 2) :
    ((ideleLoc K L w).hom) (((h2map (levelIncl K L S)).hom) a_S)
      = ((groupCohomology.coindIso (k := CoeffInt.{0})
            (S := MulAction.stabilizer (L ≃ₐ[K] L) w) (localUnitsRep K L w) 2).hom)
          (((h2map (orbitCoindMapA K L w)).hom)
            (((h2map (projSupportedHom K L S (orbitStable K L w))).hom)
              (((h2map (levelToSupportedHom K L S)).hom) a_S))) := by
  have h := congrArg (fun m => m.hom a_S) (ideleLoc_level_comp S w hw)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h
  exact h

/-! ## Vanishing of the orbit components -/

/-- **The orbit component of a level class vanishes if the localisation at a representative place
vanishes.** -/
theorem orbit_component_zero (S : GStableSet K L) (w : Place L) (hw : w ∈ S.carrier)
    (a_S : groupCohomology (levelRep K L S) 2)
    (ha : ((ideleLoc K L w).hom) (((h2map (levelIncl K L S)).hom) a_S) = 0) :
    ((h2map (projSupportedHom K L S (orbitStable K L w))).hom)
      (((h2map (levelToSupportedHom K L S)).hom) a_S) = 0 := by
  obtain ⟨s, hs⟩ := orbitCoindMapA_split (K := K) (L := L) w
  have hkey : ((h2map (orbitCoindMapA K L w)).hom)
      (((h2map (projSupportedHom K L S (orbitStable K L w))).hom)
        (((h2map (levelToSupportedHom K L S)).hom) a_S)) = 0 := by
    have h := (ideleLoc_level_eq_A S w hw a_S).symm
    rw [ha] at h
    have hz0 : ((groupCohomology.coindIso (k := CoeffInt.{0})
        (S := MulAction.stabilizer (L ≃ₐ[K] L) w) (localUnitsRep K L w) 2).toLinearEquiv)
        (((h2map (orbitCoindMapA K L w)).hom)
          (((h2map (projSupportedHom K L S (orbitStable K L w))).hom)
            (((h2map (levelToSupportedHom K L S)).hom) a_S))) = 0 := by
      simpa using h
    exact (groupCohomology.coindIso (k := CoeffInt.{0})
      (S := MulAction.stabilizer (L ≃ₐ[K] L) w) (localUnitsRep K L w) 2).toLinearEquiv.injective
      (by rw [hz0, map_zero])
  have hcomp : h2map (orbitCoindMapA K L w) ≫ h2map s =
      𝟙 (groupCohomology (supportedRep K L (orbitStable K L w)) 2) := by
    rw [← h2map_comp, hs, h2map_id]
  have h6 := congrArg (fun m => m (((h2map (projSupportedHom K L S (orbitStable K L w))).hom)
      (((h2map (levelToSupportedHom K L S)).hom) a_S))) hcomp
  simp only [ModuleCat.comp_apply, ModuleCat.id_apply] at h6
  rw [hkey] at h6
  exact h6.symm.trans (map_zero (h2map s).hom)

/-- **Existence of a representative of an orbit inside a level.** -/
theorem exists_repr_of_orbit (S : GStableSet K L) (O : orbitIndexIn (K := K) (L := L) S) :
    ∃ (w : Place L) (hw : w ∈ S.carrier), O = orbitIndexOf S w hw := by
  obtain ⟨w, hw⟩ := O.2.2
  have hwmem : w ∈ S.carrier :=
    O.2.1 (by rw [hw]; exact mem_placeOrbit.mpr ⟨1, by rw [one_smul]⟩)
  exact ⟨w, hwmem, Subtype.ext (GStableSet.ext hw)⟩

/-! ## Vanishing of the projection onto the places of a level -/

/-- **The projection of a level class onto `A_S = ∏_{v ∈ S} L_vˣ` vanishes if all the localisations
at the places of `S` vanish.** -/
theorem level_proj_zero (S : GStableSet K L) (hS : S.carrier.Finite)
    (a_S : groupCohomology (levelRep K L S) 2)
    (ha : ∀ w ∈ S.carrier, ((ideleLoc K L w).hom) (((h2map (levelIncl K L S)).hom) a_S) = 0) :
    ((h2map (levelToSupportedHom K L S)).hom) a_S = 0 := by
  have hM : ∀ O : orbitIndexIn (K := K) (L := L) S,
      ((h2map (projSupportedHom K L S O.1)).hom)
        (((h2map (levelToSupportedHom K L S)).hom) a_S) = 0 := by
    intro O
    obtain ⟨w, hwS, hO⟩ := exists_repr_of_orbit S O
    subst hO
    exact orbit_component_zero S w hwS a_S (ha w hwS)
  have hπ : ∀ O : orbitIndexIn (K := K) (L := L) S,
      ((h2map (NK.RepresentationTheory.GroupCohomology.piRepEval
        (fun O : orbitIndexIn (K := K) (L := L) S => supportedRep K L O.1) O)).hom)
        (((h2map (supportedLift K L S)).hom)
          (((h2map (levelToSupportedHom K L S)).hom) a_S)) = 0 := by
    intro O
    have hsu : supportedLift K L S ≫
        NK.RepresentationTheory.GroupCohomology.piRepEval
          (fun O : orbitIndexIn (K := K) (L := L) S => supportedRep K L O.1) O
        = projSupportedHom K L S O.1 := by
      apply Rep.hom_ext
      apply Representation.IntertwiningMap.ext
      apply LinearMap.ext
      intro x
      rfl
    rw [h2map_apply_comp (supportedLift K L S)
      (NK.RepresentationTheory.GroupCohomology.piRepEval
        (fun O : orbitIndexIn (K := K) (L := L) S => supportedRep K L O.1) O)]
    rw [hsu]
    exact hM O
  have hlift : ((h2map (supportedLift K L S)).hom)
      (((h2map (levelToSupportedHom K L S)).hom) a_S) = 0 :=
    NK.RepresentationTheory.GroupCohomology.piRep_injective
      (fun O : orbitIndexIn (K := K) (L := L) S => supportedRep K L O.1) 2 _ hπ
  obtain ⟨s', hs'⟩ := supportedLift_split (K := K) (L := L) S hS
  have hcomp : h2map (supportedLift K L S) ≫ h2map s' =
      𝟙 (groupCohomology (supportedRep K L S) 2) := by
    rw [← h2map_comp, hs', h2map_id]
  have h6 := congrArg (fun m => m (((h2map (levelToSupportedHom K L S)).hom) a_S)) hcomp
  simp only [ModuleCat.comp_apply, ModuleCat.id_apply] at h6
  rw [hlift] at h6
  exact h6.symm.trans (map_zero (h2map s').hom)

/-! ## The U-side: the localisation at a place outside the level -/

/-- **The localisation at a place outside the level, computed on the coinduced model** (morphism
form).  This is the analogue of `ideleLoc_level_comp` for the local units: the localisation at
`w ∉ S` sees the component of `𝕀_L^S` supported outside `S`, whose `w`-component is a local unit,
so it factors through `𝒪_wˣ ⟶ L_wˣ`. -/
theorem ideleLoc_level_comp_U (S : GStableSet K L) (w : Place L) (hw : w ∉ S.carrier) :
    h2map (levelIncl K L S) ≫ ideleLoc K L w
      = h2map (levelToOutsideHom K L S) ≫ h2map (projOrbitUnitsHom K L S (orbitStable K L w)) ≫
        h2map (orbitCoindMapU K L w) ≫
        (groupCohomology.coindIso (k := CoeffInt.{0})
          (S := MulAction.stabilizer (L ≃ₐ[K] L) w) (localUnitsSubRep K L w) 2).hom ≫
        groupCohomology.map (MonoidHom.id (MulAction.stabilizer (L ≃ₐ[K] L) w))
          (localUnitsIncl (K := K) (L := L) w) 2 := by
  set f := (MulAction.stabilizer (L ≃ₐ[K] L) w).subtype with hf
  have h1 : h2map (levelIncl K L S) ≫ groupCohomology.map f (𝟙 (Rep.res f (ideleRep K L))) 2
      = groupCohomology.map f (𝟙 (Rep.res f (levelRep K L S))) 2 ≫
        groupCohomology.map (MonoidHom.id (MulAction.stabilizer (L ≃ₐ[K] L) w))
          (Rep.resMap f (levelIncl K L S)) 2 :=
    (groupCohomology.resNatTrans CoeffInt (f := f) 2).naturality (levelIncl K L S)
  have h2 : Rep.resMap f (levelIncl K L S) ≫ ideleToLocalUnits K L w
      = (Rep.resMap f (levelToOutsideHom K L S) ≫
          Rep.resMap f (projOrbitUnitsHom K L S (orbitStable K L w)) ≫
          orbitCoordU K L w ≫ localUnitsIncl (K := K) (L := L) w) := res_levelIncl_comp_U S w hw
  have h3 : groupCohomology.map f (𝟙 (Rep.res f (levelRep K L S))) 2 ≫
        groupCohomology.map (MonoidHom.id (MulAction.stabilizer (L ≃ₐ[K] L) w))
          (Rep.resMap f (levelToOutsideHom K L S)) 2
      = h2map (levelToOutsideHom K L S) ≫
        groupCohomology.map f (𝟙 (Rep.res f (outsideUnitsRep K L S))) 2 :=
    ((groupCohomology.resNatTrans CoeffInt (f := f) 2).naturality
      (levelToOutsideHom K L S)).symm
  have h4 : groupCohomology.map f (𝟙 (Rep.res f (outsideUnitsRep K L S))) 2 ≫
        groupCohomology.map (MonoidHom.id (MulAction.stabilizer (L ≃ₐ[K] L) w))
          (Rep.resMap f (projOrbitUnitsHom K L S (orbitStable K L w))) 2
      = h2map (projOrbitUnitsHom K L S (orbitStable K L w)) ≫
        groupCohomology.map f
          (𝟙 (Rep.res f (orbitUnitsRep K L (orbitStable K L w)))) 2 :=
    ((groupCohomology.resNatTrans CoeffInt (f := f) 2).naturality
      (projOrbitUnitsHom K L S (orbitStable K L w))).symm
  have h5a : groupCohomology.map f
        (𝟙 (Rep.res f (orbitUnitsRep K L (orbitStable K L w)))) 2 ≫
        groupCohomology.map (MonoidHom.id (MulAction.stabilizer (L ≃ₐ[K] L) w))
          (orbitCoordU K L w) 2
      = h2map (orbitCoindMapU K L w) ≫
        (groupCohomology.coindIso (k := CoeffInt.{0})
          (S := MulAction.stabilizer (L ≃ₐ[K] L) w) (localUnitsSubRep K L w) 2).hom := by
    have hnatOC : h2map (orbitCoindMapU K L w) ≫
          (groupCohomology.resNatTrans CoeffInt (f := f) 2).app
            (Rep.coind (MulAction.stabilizer (L ≃ₐ[K] L) w).subtype (localUnitsSubRep K L w))
        = (groupCohomology.resNatTrans CoeffInt (f := f) 2).app
            (orbitUnitsRep K L (orbitStable K L w)) ≫
          groupCohomology.map (MonoidHom.id (MulAction.stabilizer (L ≃ₐ[K] L) w))
            (Rep.resMap f (orbitCoindMapU K L w)) 2 := by
      simpa only [h2map, groupCohomology.functor_map, Functor.comp_map, Functor.comp_obj,
        groupCohomology.functor_obj, Rep.resMap] using
        (groupCohomology.resNatTrans CoeffInt (f := f) 2).naturality (orbitCoindMapU K L w)
    have htri : Rep.resMap (MulAction.stabilizer (L ≃ₐ[K] L) w).subtype
          (orbitCoindMapU K L w) ≫
          (Rep.resCoindAdjunction CoeffInt.{0}
            (MulAction.stabilizer (L ≃ₐ[K] L) w).subtype).counit.app (localUnitsSubRep K L w)
        = orbitCoordU K L w :=
      res_coindToHom_counit w (orbitUnitsRep K L (orbitStable K L w)) (localUnitsSubRep K L w)
        (orbitCoordU K L w)
    rw [← NK.RepresentationTheory.GroupCohomology.res_counit_eq_coindIso
      (MulAction.stabilizer (L ≃ₐ[K] L) w) (localUnitsSubRep K L w) 2]
    rw [← Category.assoc]
    rw [hnatOC]
    rw [Category.assoc]
    rw [← groupCohomology.map_id_comp (Rep.resMap f (orbitCoindMapU K L w))
      ((Rep.resCoindAdjunction CoeffInt.{0}
        (MulAction.stabilizer (L ≃ₐ[K] L) w).subtype).counit.app (localUnitsSubRep K L w)) 2]
    rw [htri]
    simp only [groupCohomology.resNatTrans_app]
  have h5 : groupCohomology.map f
        (𝟙 (Rep.res f (orbitUnitsRep K L (orbitStable K L w)))) 2 ≫
        (groupCohomology.map (MonoidHom.id (MulAction.stabilizer (L ≃ₐ[K] L) w))
          (orbitCoordU K L w) 2 ≫
        groupCohomology.map (MonoidHom.id (MulAction.stabilizer (L ≃ₐ[K] L) w))
          (localUnitsIncl (K := K) (L := L) w) 2)
      = h2map (orbitCoindMapU K L w) ≫
        ((groupCohomology.coindIso (k := CoeffInt.{0})
          (S := MulAction.stabilizer (L ≃ₐ[K] L) w) (localUnitsSubRep K L w) 2).hom ≫
        groupCohomology.map (MonoidHom.id (MulAction.stabilizer (L ≃ₐ[K] L) w))
          (localUnitsIncl (K := K) (L := L) w) 2) := by
    rw [← Category.assoc, h5a, Category.assoc]
  calc h2map (levelIncl K L S) ≫ ideleLoc K L w
      = (h2map (levelIncl K L S) ≫
          groupCohomology.map f (𝟙 (Rep.res f (ideleRep K L))) 2) ≫
          groupCohomology.map (MonoidHom.id (MulAction.stabilizer (L ≃ₐ[K] L) w))
            (ideleToLocalUnits K L w) 2 := by
        rw [show ideleLoc K L w = groupCohomology.map f (𝟙 (Rep.res f (ideleRep K L))) 2 ≫
          groupCohomology.map (MonoidHom.id (MulAction.stabilizer (L ≃ₐ[K] L) w))
            (ideleToLocalUnits K L w) 2 from rfl, ← Category.assoc]
    _ = (groupCohomology.map f (𝟙 (Rep.res f (levelRep K L S))) 2 ≫
          groupCohomology.map (MonoidHom.id (MulAction.stabilizer (L ≃ₐ[K] L) w))
            (Rep.resMap f (levelIncl K L S)) 2) ≫
          groupCohomology.map (MonoidHom.id (MulAction.stabilizer (L ≃ₐ[K] L) w))
            (ideleToLocalUnits K L w) 2 := by
        rw [h1]
    _ = groupCohomology.map f (𝟙 (Rep.res f (levelRep K L S))) 2 ≫
          groupCohomology.map (MonoidHom.id (MulAction.stabilizer (L ≃ₐ[K] L) w))
            (Rep.resMap f (levelIncl K L S) ≫ ideleToLocalUnits K L w) 2 := by
        rw [Category.assoc, ← groupCohomology.map_id_comp (Rep.resMap f (levelIncl K L S))
          (ideleToLocalUnits K L w) 2]
    _ = groupCohomology.map f (𝟙 (Rep.res f (levelRep K L S))) 2 ≫
          groupCohomology.map (MonoidHom.id (MulAction.stabilizer (L ≃ₐ[K] L) w))
            (Rep.resMap f (levelToOutsideHom K L S) ≫
              Rep.resMap f (projOrbitUnitsHom K L S (orbitStable K L w)) ≫
              (orbitCoordU K L w ≫ localUnitsIncl (K := K) (L := L) w)) 2 := by
        rw [h2]
    _ = (groupCohomology.map f (𝟙 (Rep.res f (levelRep K L S))) 2 ≫
          groupCohomology.map (MonoidHom.id (MulAction.stabilizer (L ≃ₐ[K] L) w))
            (Rep.resMap f (levelToOutsideHom K L S)) 2) ≫
          (groupCohomology.map (MonoidHom.id (MulAction.stabilizer (L ≃ₐ[K] L) w))
            (Rep.resMap f (projOrbitUnitsHom K L S (orbitStable K L w))) 2 ≫
          (groupCohomology.map (MonoidHom.id (MulAction.stabilizer (L ≃ₐ[K] L) w))
            (orbitCoordU K L w) 2 ≫
          groupCohomology.map (MonoidHom.id (MulAction.stabilizer (L ≃ₐ[K] L) w))
            (localUnitsIncl (K := K) (L := L) w) 2)) := by
        rw [groupCohomology.map_id_comp (Rep.resMap f (levelToOutsideHom K L S))
            (Rep.resMap f (projOrbitUnitsHom K L S (orbitStable K L w)) ≫
              (orbitCoordU K L w ≫ localUnitsIncl (K := K) (L := L) w)) 2,
          groupCohomology.map_id_comp (Rep.resMap f (projOrbitUnitsHom K L S (orbitStable K L w)))
            (orbitCoordU K L w ≫ localUnitsIncl (K := K) (L := L) w) 2,
          groupCohomology.map_id_comp (orbitCoordU K L w) (localUnitsIncl (K := K) (L := L) w) 2,
          ← Category.assoc]
    _ = (h2map (levelToOutsideHom K L S) ≫
          groupCohomology.map f (𝟙 (Rep.res f (outsideUnitsRep K L S))) 2) ≫
          (groupCohomology.map (MonoidHom.id (MulAction.stabilizer (L ≃ₐ[K] L) w))
            (Rep.resMap f (projOrbitUnitsHom K L S (orbitStable K L w))) 2 ≫
          (groupCohomology.map (MonoidHom.id (MulAction.stabilizer (L ≃ₐ[K] L) w))
            (orbitCoordU K L w) 2 ≫
          groupCohomology.map (MonoidHom.id (MulAction.stabilizer (L ≃ₐ[K] L) w))
            (localUnitsIncl (K := K) (L := L) w) 2)) := by
        rw [h3]
    _ = h2map (levelToOutsideHom K L S) ≫
          ((groupCohomology.map f (𝟙 (Rep.res f (outsideUnitsRep K L S))) 2 ≫
            groupCohomology.map (MonoidHom.id (MulAction.stabilizer (L ≃ₐ[K] L) w))
              (Rep.resMap f (projOrbitUnitsHom K L S (orbitStable K L w))) 2) ≫
          (groupCohomology.map (MonoidHom.id (MulAction.stabilizer (L ≃ₐ[K] L) w))
            (orbitCoordU K L w) 2 ≫
          groupCohomology.map (MonoidHom.id (MulAction.stabilizer (L ≃ₐ[K] L) w))
            (localUnitsIncl (K := K) (L := L) w) 2)) := by
        simp only [Category.assoc]
    _ = h2map (levelToOutsideHom K L S) ≫
          ((h2map (projOrbitUnitsHom K L S (orbitStable K L w)) ≫
            groupCohomology.map f
              (𝟙 (Rep.res f (orbitUnitsRep K L (orbitStable K L w)))) 2) ≫
          (groupCohomology.map (MonoidHom.id (MulAction.stabilizer (L ≃ₐ[K] L) w))
            (orbitCoordU K L w) 2 ≫
          groupCohomology.map (MonoidHom.id (MulAction.stabilizer (L ≃ₐ[K] L) w))
            (localUnitsIncl (K := K) (L := L) w) 2)) := by
        rw [h4]
    _ = h2map (levelToOutsideHom K L S) ≫
          (h2map (projOrbitUnitsHom K L S (orbitStable K L w)) ≫
          (groupCohomology.map f
              (𝟙 (Rep.res f (orbitUnitsRep K L (orbitStable K L w)))) 2 ≫
          (groupCohomology.map (MonoidHom.id (MulAction.stabilizer (L ≃ₐ[K] L) w))
            (orbitCoordU K L w) 2 ≫
          groupCohomology.map (MonoidHom.id (MulAction.stabilizer (L ≃ₐ[K] L) w))
            (localUnitsIncl (K := K) (L := L) w) 2))) := by
        rw [Category.assoc]
    _ = h2map (levelToOutsideHom K L S) ≫
          (h2map (projOrbitUnitsHom K L S (orbitStable K L w)) ≫
          (h2map (orbitCoindMapU K L w) ≫
          ((groupCohomology.coindIso (k := CoeffInt.{0})
            (S := MulAction.stabilizer (L ≃ₐ[K] L) w) (localUnitsSubRep K L w) 2).hom ≫
          groupCohomology.map (MonoidHom.id (MulAction.stabilizer (L ≃ₐ[K] L) w))
            (localUnitsIncl (K := K) (L := L) w) 2))) := by
        rw [h5]

/-- **The `U`-component of a level class vanishes if the localisation at a representative place
outside the level vanishes.** -/
theorem orbit_component_zero_U (S : GStableSet K L) (w : Place L) (hw : w ∉ S.carrier)
    (a_S : groupCohomology (levelRep K L S) 2)
    (ha : ((ideleLoc K L w).hom) (((h2map (levelIncl K L S)).hom) a_S) = 0) :
    ((h2map (projOrbitUnitsHom K L S (orbitStable K L w))).hom)
      (((h2map (levelToOutsideHom K L S)).hom) a_S) = 0 := by
  obtain ⟨s, hs⟩ := orbitCoindMapU_split (K := K) (L := L) w
  have hinj : Function.Injective (fun x => ((groupCohomology.functor CoeffInt.{0}
      (MulAction.stabilizer (L ≃ₐ[K] L) w) 2).map
        (localUnitsIncl (K := K) (L := L) w)).hom x) :=
    localUnits_h2_injective (K := K) (L := L) w
  have hloc : ((ideleLoc K L w).hom) (((h2map (levelIncl K L S)).hom) a_S)
      = ((groupCohomology.functor CoeffInt.{0} (MulAction.stabilizer (L ≃ₐ[K] L) w) 2).map
            (localUnitsIncl (K := K) (L := L) w)).hom
          (((groupCohomology.coindIso (k := CoeffInt.{0})
              (S := MulAction.stabilizer (L ≃ₐ[K] L) w) (localUnitsSubRep K L w) 2).hom)
            (((h2map (orbitCoindMapU K L w)).hom)
              (((h2map (projOrbitUnitsHom K L S (orbitStable K L w))).hom)
                (((h2map (levelToOutsideHom K L S)).hom) a_S)))) := by
    have h1 := congrArg (fun m => m.hom) (ideleLoc_level_comp_U S w hw)
    rw [ModuleCat.hom_comp, ModuleCat.hom_comp, ModuleCat.hom_comp, ModuleCat.hom_comp,
      ModuleCat.hom_comp] at h1
    have h2 := LinearMap.congr_fun h1 a_S
    rw [LinearMap.comp_apply, LinearMap.comp_apply, LinearMap.comp_apply, LinearMap.comp_apply,
      LinearMap.comp_apply] at h2
    exact h2
  have hkey : ((h2map (orbitCoindMapU K L w)).hom)
      (((h2map (projOrbitUnitsHom K L S (orbitStable K L w))).hom)
        (((h2map (levelToOutsideHom K L S)).hom) a_S)) = 0 := by
    have h0 : ((groupCohomology.functor CoeffInt.{0}
          (MulAction.stabilizer (L ≃ₐ[K] L) w) 2).map
            (localUnitsIncl (K := K) (L := L) w)).hom
          (((groupCohomology.coindIso (k := CoeffInt.{0})
              (S := MulAction.stabilizer (L ≃ₐ[K] L) w) (localUnitsSubRep K L w) 2).hom)
            (((h2map (orbitCoindMapU K L w)).hom)
              (((h2map (projOrbitUnitsHom K L S (orbitStable K L w))).hom)
                (((h2map (levelToOutsideHom K L S)).hom) a_S)))) = 0 := by
      rw [← hloc]
      exact ha
    have h1 : ((groupCohomology.coindIso (k := CoeffInt.{0})
          (S := MulAction.stabilizer (L ≃ₐ[K] L) w) (localUnitsSubRep K L w) 2).hom)
          (((h2map (orbitCoindMapU K L w)).hom)
            (((h2map (projOrbitUnitsHom K L S (orbitStable K L w))).hom)
              (((h2map (levelToOutsideHom K L S)).hom) a_S))) = 0 := by
      refine hinj ?_
      show ((groupCohomology.functor CoeffInt.{0} (MulAction.stabilizer (L ≃ₐ[K] L) w) 2).map
            (localUnitsIncl (K := K) (L := L) w)).hom
          (((groupCohomology.coindIso (k := CoeffInt.{0})
              (S := MulAction.stabilizer (L ≃ₐ[K] L) w) (localUnitsSubRep K L w) 2).hom)
            (((h2map (orbitCoindMapU K L w)).hom)
              (((h2map (projOrbitUnitsHom K L S (orbitStable K L w))).hom)
                (((h2map (levelToOutsideHom K L S)).hom) a_S))))
        = ((groupCohomology.functor CoeffInt.{0} (MulAction.stabilizer (L ≃ₐ[K] L) w) 2).map
            (localUnitsIncl (K := K) (L := L) w)).hom 0
      rw [h0, map_zero]
    have hz0 : ((groupCohomology.coindIso (k := CoeffInt.{0})
        (S := MulAction.stabilizer (L ≃ₐ[K] L) w) (localUnitsSubRep K L w) 2).toLinearEquiv)
        (((h2map (orbitCoindMapU K L w)).hom)
          (((h2map (projOrbitUnitsHom K L S (orbitStable K L w))).hom)
            (((h2map (levelToOutsideHom K L S)).hom) a_S))) = 0 := by
      simpa using h1
    exact (groupCohomology.coindIso (k := CoeffInt.{0})
      (S := MulAction.stabilizer (L ≃ₐ[K] L) w) (localUnitsSubRep K L w) 2).toLinearEquiv.injective
      (by rw [hz0, map_zero])
  have hcomp : h2map (orbitCoindMapU K L w) ≫ h2map s =
      𝟙 (groupCohomology (orbitUnitsRep K L (orbitStable K L w)) 2) := by
    rw [← h2map_comp, hs, h2map_id]
  have h6 := congrArg (fun m => m (((h2map (projOrbitUnitsHom K L S (orbitStable K L w))).hom)
      (((h2map (levelToOutsideHom K L S)).hom) a_S))) hcomp
  simp only [ModuleCat.comp_apply, ModuleCat.id_apply] at h6
  rw [hkey] at h6
  exact h6.symm.trans (map_zero (h2map s).hom)

/-- **Existence of a representative of an orbit disjoint from a level.** -/
theorem exists_repr_of_orbitOut (S : GStableSet K L) (O : orbitIndexOut (K := K) (L := L) S) :
    ∃ (w : Place L) (hw : w ∉ S.carrier), O = orbitOfOut S w hw := by
  obtain ⟨w, hw⟩ := O.2.1
  have hwS : w ∉ S.carrier := by
    intro h
    exact Set.disjoint_left.mp O.2.2
      (by rw [hw]; exact mem_placeOrbit.mpr ⟨1, by rw [one_smul]⟩) h
  exact ⟨w, hwS, Subtype.ext (GStableSet.ext (by rw [orbitOfOut_carrier]; exact hw))⟩

/-- **The projection of a level class onto the local units outside the level vanishes if all the
localisations at the places outside the level vanish.** -/
theorem level_outside_zero (S : GStableSet K L) (hS : S.carrier.Finite)
    (a_S : groupCohomology (levelRep K L S) 2)
    (ha : ∀ w ∉ S.carrier, ((ideleLoc K L w).hom) (((h2map (levelIncl K L S)).hom) a_S) = 0) :
    ((h2map (levelToOutsideHom K L S)).hom) a_S = 0 := by
  have hM : ∀ O : orbitIndexOut (K := K) (L := L) S,
      ((h2map (projOrbitUnitsHom K L S O.1)).hom)
        (((h2map (levelToOutsideHom K L S)).hom) a_S) = 0 := by
    intro O
    obtain ⟨w, hwS, hO⟩ := exists_repr_of_orbitOut S O
    subst hO
    exact orbit_component_zero_U S w hwS a_S (ha w hwS)
  have hπ : ∀ O : orbitIndexOut (K := K) (L := L) S,
      ((h2map (NK.RepresentationTheory.GroupCohomology.piRepEval
        (fun O : orbitIndexOut (K := K) (L := L) S => orbitUnitsRep K L O.1) O)).hom)
        (((h2map (outsideUnitsLift K L S)).hom)
          (((h2map (levelToOutsideHom K L S)).hom) a_S)) = 0 := by
    intro O
    have hsu : outsideUnitsLift K L S ≫
        NK.RepresentationTheory.GroupCohomology.piRepEval
          (fun O : orbitIndexOut (K := K) (L := L) S => orbitUnitsRep K L O.1) O
        = projOrbitUnitsHom K L S O.1 := by
      apply Rep.hom_ext
      apply Representation.IntertwiningMap.ext
      apply LinearMap.ext
      intro x
      rfl
    rw [h2map_apply_comp (outsideUnitsLift K L S)
      (NK.RepresentationTheory.GroupCohomology.piRepEval
        (fun O : orbitIndexOut (K := K) (L := L) S => orbitUnitsRep K L O.1) O)]
    rw [hsu]
    exact hM O
  have hlift : ((h2map (outsideUnitsLift K L S)).hom)
      (((h2map (levelToOutsideHom K L S)).hom) a_S) = 0 :=
    NK.RepresentationTheory.GroupCohomology.piRep_injective
      (fun O : orbitIndexOut (K := K) (L := L) S => orbitUnitsRep K L O.1) 2 _ hπ
  obtain ⟨s', hs'⟩ := outsideUnitsLift_split (K := K) (L := L) S
  have hcomp : h2map (outsideUnitsLift K L S) ≫ h2map s' =
      𝟙 (groupCohomology (outsideUnitsRep K L S) 2) := by
    rw [← h2map_comp, hs', h2map_id]
  have h6 := congrArg (fun m => m (((h2map (levelToOutsideHom K L S)).hom) a_S)) hcomp
  simp only [ModuleCat.comp_apply, ModuleCat.id_apply] at h6
  rw [hlift] at h6
  exact h6.symm.trans (map_zero (h2map s').hom)

/-! ## The decomposition of a level into its two summands -/

/-- **The two summands of a level multiply back to the level class**: the product of the idèles
supported on `S` with the local units outside `S` is the idèle itself. -/
theorem level_decomposition_apply (S : GStableSet K L) (y : ↥(levelSubgroup S.carrier)) :
    (Subgroup.inclusion (supportedSubgroup_le_level K L (S := S))
        (levelToSupported K L S y)) *
      (Subgroup.inclusion (orbitUnitsSubgroup_le_level K L (S := S))
        (levelToOutside K L S y)) = y := by
  apply Subtype.ext
  show ((levelToSupported K L S y : ↥(supportedSubgroup S.carrier)) : Idele L) *
      ((levelToOutside K L S y : ↥(orbitUnitsSubgroup (K := K) S.compl.carrier)) : Idele L)
    = (y : Idele L)
  rw [show ((levelToSupported K L S y : ↥(supportedSubgroup S.carrier)) : Idele L)
      = restrictTo K L S.carrier (y : Idele L) from rfl]
  rw [show ((levelToOutside K L S y : ↥(orbitUnitsSubgroup (K := K) S.compl.carrier)) : Idele L)
      = (y : Idele L) * (restrictTo K L S.carrier (y : Idele L))⁻¹ from rfl]
  rw [← mul_assoc, mul_comm (restrictTo K L S.carrier (y : Idele L)) (y : Idele L), mul_assoc,
    mul_inv_cancel, mul_one]

/-- **The level `𝕀_L^S` is the product of the idèles supported on `S` and the local units outside
`S`**: the two projections are the components of an isomorphism, so the sum of the corresponding
idempotents is the identity. -/
theorem level_decomposition (S : GStableSet K L) :
    levelToSupportedHom K L S ≫ inclSupported K L S +
      levelToOutsideHom K L S ≫ inclOutsideUnits K L S = 𝟙 (levelRep K L S) := by
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro x
  rw [Rep.add_hom, Representation.IntertwiningMap.add_toLinearMap, LinearMap.add_apply]
  rw [Rep.hom_comp, Rep.hom_comp, Representation.IntertwiningMap.comp_toLinearMap,
    Representation.IntertwiningMap.comp_toLinearMap, LinearMap.comp_apply, LinearMap.comp_apply]
  exact level_decomposition_apply S x

/-! ## Additivity of the induced map on `H²` -/

/-- The pointwise addition of morphisms of representations. -/
theorem rep_add_apply {M N : Rep.{0, 0, 0} CoeffInt.{0} (L ≃ₐ[K] L)} (f g : M ⟶ N) (x : M.V) :
    (f + g) x = f x + g x := by
  change (((f + g).hom).toLinearMap) x = ((f.hom).toLinearMap) x + ((g.hom).toLinearMap) x
  rw [Rep.add_hom, Representation.IntertwiningMap.add_toLinearMap, LinearMap.add_apply]

/-- **The map induced by a morphism of representations on `H²` is additive in the morphism.** -/
theorem h2map_add {M N : Rep.{0, 0, 0} CoeffInt.{0} (L ≃ₐ[K] L)} (f g : M ⟶ N) :
    h2map (f + g) = h2map f + h2map g := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro a
  obtain ⟨z, hz⟩ := (ModuleCat.epi_iff_surjective (groupCohomology.H2π M)).1 inferInstance a
  rw [← hz]
  rw [ModuleCat.hom_add, LinearMap.add_apply]
  simp only [h2map, groupCohomology.functor_map]
  rw [groupCohomology.H2π_comp_map_apply (MonoidHom.id (L ≃ₐ[K] L)) (f + g) z,
    groupCohomology.H2π_comp_map_apply (MonoidHom.id (L ≃ₐ[K] L)) f z,
    groupCohomology.H2π_comp_map_apply (MonoidHom.id (L ≃ₐ[K] L)) g z]
  rw [← map_add]
  congr 1

/-! ## The Hasse principle for the idèles -/

/-- **Shapiro's result for the idèles**: the localisation `H²(Gal(L/K), 𝕀_L) ⟶ ∏_w H²(Γ_w, L_wˣ)`
is injective. -/
theorem hbnIdele_proof : HBNIdele K L := by
  intro a ha
  obtain ⟨S, hS, a_S, haS⟩ := exists_level_of_h2 (K := K) (L := L) a
  have haS' : ((h2map (levelIncl K L S)).hom) a_S = a := haS
  have hzA : ((h2map (levelToSupportedHom K L S)).hom) a_S = 0 :=
    level_proj_zero S hS a_S (fun w _ => by rw [haS']; exact ha w)
  have hzU : ((h2map (levelToOutsideHom K L S)).hom) a_S = 0 :=
    level_outside_zero S hS a_S (fun w _ => by rw [haS']; exact ha w)
  have hsum : (h2map (levelToSupportedHom K L S) ≫ h2map (inclSupported K L S)) +
      (h2map (levelToOutsideHom K L S) ≫ h2map (inclOutsideUnits K L S)) =
      𝟙 (groupCohomology (levelRep K L S) 2) := by
    rw [← h2map_comp, ← h2map_comp, ← h2map_add, level_decomposition S, h2map_id]
  have h6 := congrArg (fun m => m.hom a_S) hsum
  rw [ModuleCat.hom_add, LinearMap.add_apply, ModuleCat.comp_apply, ModuleCat.comp_apply,
    ModuleCat.id_apply] at h6
  rw [hzA, hzU] at h6
  simp only [map_zero, zero_add] at h6
  have hzero : a_S = 0 := h6.symm
  rw [← haS', hzero]
  exact map_zero (h2map (levelIncl K L S)).hom

end

end NK.HassePrinciple
