/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The orbit layer of the idèles: `Γ`-stable subgroups of `𝕀_L` as `CoeffInt`-representations

This module builds the coefficient layer of `NK.HassePrinciple.hbnIdele` (Shapiro's lemma for
the idèles): the `Gal(L/K)`-stable subgroups of the idèle group `𝕀_L` that occur in the proof,
together with their `CoeffInt`-linear representation structure.

* `NK.HassePrinciple.unitySubgroup` — the idèles all of whose components are local units
  (`∏_v 𝒪_vˣ`);
* `NK.HassePrinciple.supportedSubgroup O` — the idèles supported on a set `O` of places;
* `NK.HassePrinciple.levelSubgroup S` — the level `𝕀_L^S` of idèles that are local units outside
  `S`;
* `NK.HassePrinciple.orbitUnitsSubgroup O` — their intersection: the idèles supported on `O`
  whose components are local units (`∏_{v ∈ O} 𝒪_vˣ`).

Each of them is `Gal(L/K)`-stable as soon as the underlying set of places is, and the action of
`Gal(L/K)` on the ambient idèle group restricts to a `MulDistribMulAction` on the subgroup; hence
`Rep.ofDistribMulAction` endows each of them with the structure of a `CoeffInt`-linear
representation of `Gal(L/K)`.
-/

import Mathlib
import Submission.NK.HassePrinciple.LocalUnitsSub
import Submission.NK.HassePrinciple.LocalUnits
import Submission.NK.HassePrinciple.IdelesLevel
import Submission.NK.HassePrinciple.IdeleCocycle
import Submission.NK.HassePrinciple.exists_idele_coboundary_of_isMulCocycle
import Submission.NK.RepresentationTheory.GroupCohomology.res_counit_eq_coindIso
import Submission.NK.RepresentationTheory.GroupCohomology.piCohomology_injective

namespace NK.HassePrinciple

open CategoryTheory Representation
open NK.GlobalCFT
open scoped NumberField

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L]

/-! ## Transport lemmas for the action on the idèles -/

/-- Membership in the local units at `g • w` is the transport of membership at `w` along the local
isomorphism. -/
theorem actVal_mem_localUnits_iff (g : L ≃ₐ[K] L) (w : Place L)
    (u : (Place.localField L w)ˣ) :
    u ∈ Place.localUnits L w ↔ actVal g w u ∈ Place.localUnits L (g • w) :=
  Place.localRingEquiv_mem_localUnits g w u

/-- The component of a translate of an idèle, expressed through `actVal`. -/
theorem smul_apply_eq_actVal (σ : L ≃ₐ[K] L) (x : Idele L) (w : Place L) :
    (σ • x) w = (smul_inv_smul σ w) ▸ actVal σ (σ⁻¹ • w) (x (σ⁻¹ • w)) := by
  have h := smul_apply_smul_place (K := K) σ (σ⁻¹ • w) x
  have h1 : (smul_inv_smul σ w) ▸ ((σ • x) (σ • (σ⁻¹ • w))) = (σ • x) w :=
    units_transport (smul_inv_smul σ w) (σ • x)
  rw [← h1]
  exact congrArg (fun z => (smul_inv_smul σ w) ▸ z) h

/-- Transport of the unit `1` along an equality of places. -/
theorem cast_one {a b : Place L} (h : a = b) :
    (h ▸ (1 : (Place.localField L a)ˣ)) = (1 : (Place.localField L b)ˣ) := by
  cases h; rfl

/-! ## `Γ`-stable subgroups of `𝕀_L` -/

/-- **The unity idèles** `∏_v 𝒪_vˣ`: the idèles all of whose local components are local units. -/
def unitySubgroup (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] : Subgroup (Idele L) where
  carrier := {x | ∀ v : Place L, x v ∈ Place.localUnits L v}
  mul_mem' := by
    intro x y hx hy v
    rw [Idele.mul_apply]
    exact mul_mem (hx v) (hy v)
  one_mem' := by intro v; rw [Idele.one_apply]; exact one_mem _
  inv_mem' := by intro x hx v; rw [Idele.inv_apply]; exact inv_mem (hx v)

@[simp] theorem mem_unitySubgroup {x : Idele L} :
    x ∈ unitySubgroup K L ↔ ∀ v : Place L, x v ∈ Place.localUnits L v := Iff.rfl

/-- **The idèles supported on `O`**: those that are `1` at every place outside `O`. -/
def supportedSubgroup (O : Set (Place L)) : Subgroup (Idele L) where
  carrier := {x | ∀ v : Place L, v ∉ O → x v = 1}
  mul_mem' := by
    intro x y hx hy v hv
    rw [Idele.mul_apply, hx v hv, hy v hv, one_mul]
  one_mem' := by intro v _; rw [Idele.one_apply]
  inv_mem' := by
    intro x hx v hv
    rw [Idele.inv_apply, hx v hv, inv_one]

@[simp] theorem mem_supportedSubgroup {O : Set (Place L)} {x : Idele L} :
    x ∈ supportedSubgroup O ↔ ∀ v : Place L, v ∉ O → x v = 1 := Iff.rfl

/-- **The level `𝕀_L^S`**: the idèles that are local units outside `S`. -/
def levelSubgroup (S : Set (Place L)) : Subgroup (Idele L) where
  carrier := {x | ∀ v : Place L, v ∉ S → x v ∈ Place.localUnits L v}
  mul_mem' := by
    intro x y hx hy v hv
    rw [Idele.mul_apply]
    exact mul_mem (hx v hv) (hy v hv)
  one_mem' := by intro v _; rw [Idele.one_apply]; exact one_mem _
  inv_mem' := by intro x hx v hv; rw [Idele.inv_apply]; exact inv_mem (hx v hv)

@[simp] theorem mem_levelSubgroup {S : Set (Place L)} {x : Idele L} :
    x ∈ levelSubgroup S ↔ ∀ v : Place L, v ∉ S → x v ∈ Place.localUnits L v := Iff.rfl

/-- **The idèles supported on `O` with local-unit components** (`∏_{v ∈ O} 𝒪_vˣ`). -/
def orbitUnitsSubgroup (O : Set (Place L)) : Subgroup (Idele L) :=
  supportedSubgroup O ⊓ unitySubgroup K L

theorem mem_orbitUnitsSubgroup {O : Set (Place L)} {x : Idele L} :
    x ∈ orbitUnitsSubgroup (K := K) O ↔
      (∀ v : Place L, v ∉ O → x v = 1) ∧ (∀ v : Place L, x v ∈ Place.localUnits L v) := by
  rw [orbitUnitsSubgroup, Subgroup.mem_inf, mem_supportedSubgroup, mem_unitySubgroup]

/-! ## Stability of the subgroups under `Gal(L/K)` -/

set_option backward.isDefEq.respectTransparency false in

theorem smul_mem_unitySubgroup {x : Idele L} (hx : x ∈ unitySubgroup K L) (σ : L ≃ₐ[K] L) :
    σ • x ∈ unitySubgroup K L := by
  rw [mem_unitySubgroup] at hx ⊢
  intro v
  rw [smul_apply_eq_actVal]
  exact (mem_localUnits_of_eq' (smul_inv_smul σ v) _).mp
    ((actVal_mem_localUnits_iff σ (σ⁻¹ • v) (x (σ⁻¹ • v))).mp (hx (σ⁻¹ • v)))

/-- **The `Gal(L/K)`-orbit of a place**, as a set of places. -/
def placeOrbit (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] (w : Place L) : Set (Place L) :=
  MulAction.orbit (L ≃ₐ[K] L) w

@[simp] theorem mem_placeOrbit {w v : Place L} :
    v ∈ placeOrbit K L w ↔ ∃ g : L ≃ₐ[K] L, g • w = v := MulAction.mem_orbit_iff

theorem orbit_smul_mem (w : Place L) (σ : L ≃ₐ[K] L) ⦃v : Place L⦄
    (hv : v ∈ placeOrbit K L w) : σ • v ∈ placeOrbit K L w := by
  obtain ⟨g, rfl⟩ := MulAction.mem_orbit_iff.mp hv
  exact MulAction.mem_orbit_iff.mpr ⟨σ * g, by rw [mul_smul]⟩

theorem smul_mem_supportedSubgroup {O : Set (Place L)}
    (hO : ∀ (σ : L ≃ₐ[K] L) ⦃v : Place L⦄, v ∈ O → σ • v ∈ O)
    {x : Idele L} (hx : x ∈ supportedSubgroup O) (σ : L ≃ₐ[K] L) :
    σ • x ∈ supportedSubgroup O := by
  rw [mem_supportedSubgroup] at hx ⊢
  intro v hv
  have hv' : σ⁻¹ • v ∉ O := fun h => hv (by
    have hh := hO σ h
    rwa [smul_inv_smul] at hh)
  rw [smul_apply_eq_actVal, hx (σ⁻¹ • v) hv', actVal_one]
  exact cast_one _

theorem smul_mem_levelSubgroup {S : Set (Place L)}
    (hS : ∀ (σ : L ≃ₐ[K] L) ⦃v : Place L⦄, v ∈ S → σ • v ∈ S)
    {x : Idele L} (hx : x ∈ levelSubgroup S) (σ : L ≃ₐ[K] L) :
    σ • x ∈ levelSubgroup S := by
  rw [mem_levelSubgroup] at hx ⊢
  intro v hv
  have hv' : σ⁻¹ • v ∉ S := fun h => hv (by
    have hh := hS σ h
    rwa [smul_inv_smul] at hh)
  rw [smul_apply_eq_actVal]
  exact (mem_localUnits_of_eq' (smul_inv_smul σ v) _).mp
    ((actVal_mem_localUnits_iff σ (σ⁻¹ • v) (x (σ⁻¹ • v))).mp (hx (σ⁻¹ • v) hv'))

theorem smul_mem_orbitUnitsSubgroup {O : Set (Place L)}
    (hO : ∀ (σ : L ≃ₐ[K] L) ⦃v : Place L⦄, v ∈ O → σ • v ∈ O)
    {x : Idele L} (hx : x ∈ orbitUnitsSubgroup (K := K) O) (σ : L ≃ₐ[K] L) :
    σ • x ∈ orbitUnitsSubgroup (K := K) O := by
  rw [mem_orbitUnitsSubgroup] at hx ⊢
  exact ⟨smul_mem_supportedSubgroup hO hx.1 σ, smul_mem_unitySubgroup hx.2 σ⟩

/-! ## Bundled stable sets -/

/-- A `Gal(L/K)`-stable set of places.  The representation-theoretic constructions below are
parametrised by such a set, so that the stability hypothesis can be found by typeclass search. -/
structure GStableSet (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] where
  carrier : Set (Place L)
  smul_mem' : ∀ (σ : L ≃ₐ[K] L) ⦃v : Place L⦄, v ∈ carrier → σ • v ∈ carrier

/-! ## The representation structure -/

/-- **The `MulDistribMulAction` of `Γ` on a `Γ`-stable subgroup of `𝕀_L`**, obtained by
restricting the action on the idèles. -/
def subgroupAction (N : Subgroup (Idele L))
    (hN : ∀ (σ : L ≃ₐ[K] L) ⦃x : Idele L⦄, x ∈ N → σ • x ∈ N) :
    MulDistribMulAction (L ≃ₐ[K] L) ↥N where
  smul σ x := ⟨σ • (x : Idele L), hN σ x.2⟩
  one_smul x := Subtype.ext (one_smul (L ≃ₐ[K] L) (x : Idele L))
  mul_smul σ τ x := Subtype.ext (mul_smul σ τ (x : Idele L))
  smul_mul σ x y :=
    Subtype.ext (MulDistribMulAction.smul_mul σ (x : Idele L) (y : Idele L))
  smul_one σ := Subtype.ext (smul_one σ)

instance instMulDistribMulActionUnitySubgroup :
    MulDistribMulAction (L ≃ₐ[K] L) ↥(unitySubgroup K L) :=
  subgroupAction _ fun σ x hx => smul_mem_unitySubgroup hx σ

instance instMulDistribMulActionOrbitSupportedSubgroup (w : Place L) :
    MulDistribMulAction (L ≃ₐ[K] L) ↥(supportedSubgroup (placeOrbit K L w)) :=
  subgroupAction _ fun σ x hx => smul_mem_supportedSubgroup (orbit_smul_mem w) hx σ

instance instMulDistribMulActionOrbitUnitsOrbit (w : Place L) :
    MulDistribMulAction (L ≃ₐ[K] L) ↥(orbitUnitsSubgroup (K := K) (placeOrbit K L w)) :=
  subgroupAction _ fun σ x hx => smul_mem_orbitUnitsSubgroup (orbit_smul_mem w) hx σ

instance instMulDistribMulActionSupportedSubgroup (O : GStableSet K L) :
    MulDistribMulAction (L ≃ₐ[K] L) ↥(supportedSubgroup O.carrier) :=
  subgroupAction _ fun σ x hx => smul_mem_supportedSubgroup O.smul_mem' hx σ

instance instMulDistribMulActionLevelSubgroup (S : GStableSet K L) :
    MulDistribMulAction (L ≃ₐ[K] L) ↥(levelSubgroup S.carrier) :=
  subgroupAction _ fun σ x hx => smul_mem_levelSubgroup S.smul_mem' hx σ

instance instMulDistribMulActionOrbitUnitsSubgroup (O : GStableSet K L) :
    MulDistribMulAction (L ≃ₐ[K] L) ↥(orbitUnitsSubgroup (K := K) O.carrier) :=
  subgroupAction _ fun σ x hx => smul_mem_orbitUnitsSubgroup O.smul_mem' hx σ

/-- **The unity idèles `∏_v 𝒪_vˣ`** as a `CoeffInt`-linear representation of `Gal(L/K)`. -/
noncomputable def unityRep (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L] :
    Rep.{0, 0, 0} CoeffInt.{0} (L ≃ₐ[K] L) :=
  Rep.ofDistribMulAction CoeffInt.{0} _ (Additive ↥(unitySubgroup K L))

/-- **The idèles supported on `O`** as a `CoeffInt`-linear representation of `Gal(L/K)`. -/
noncomputable def supportedRep (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L] (O : GStableSet K L) :
    Rep.{0, 0, 0} CoeffInt.{0} (L ≃ₐ[K] L) :=
  Rep.ofDistribMulAction CoeffInt.{0} _ (Additive ↥(supportedSubgroup O.carrier))

/-- **The level `𝕀_L^S`** as a `CoeffInt`-linear representation of `Gal(L/K)`. -/
noncomputable def levelRep (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L] (S : GStableSet K L) :
    Rep.{0, 0, 0} CoeffInt.{0} (L ≃ₐ[K] L) :=
  Rep.ofDistribMulAction CoeffInt.{0} _ (Additive ↥(levelSubgroup S.carrier))

/-- **The idèles supported on `O` with local-unit components** as a representation. -/
noncomputable def orbitUnitsRep (K L : Type) [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L] (O : GStableSet K L) :
    Rep.{0, 0, 0} CoeffInt.{0} (L ≃ₐ[K] L) :=
  Rep.ofDistribMulAction CoeffInt.{0} _ (Additive ↥(orbitUnitsSubgroup (K := K) O.carrier))

end

end NK.HassePrinciple
