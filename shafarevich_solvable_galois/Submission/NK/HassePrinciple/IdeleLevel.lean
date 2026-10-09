/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The level `𝕀_L^S` of the idèles and its decomposition

This module provides the *bookkeeping* layer of `NK.HassePrinciple.hbnIdele`: the level
subgroups of the idèle group on which the argument is carried out, and the maps between them.

* `NK.HassePrinciple.restrictTo` — the idèle `x` with all components outside `S` replaced by `1`;
* `NK.HassePrinciple.GStableSet.compl` — the complement of a `Gal(L/K)`-stable set of places;
* `NK.HassePrinciple.outsideUnitsRep` — the idèles supported outside `S` whose components are
  local units (`∏_{v ∉ S} 𝒪_vˣ`) as a representation;
* `NK.HassePrinciple.levelToSupported`, `...levelToOutside` — the two projections
  `𝕀_L^S ⟶ ∏_{v ∈ S} L_vˣ` and `𝕀_L^S ⟶ ∏_{v ∉ S} 𝒪_vˣ` (`x ↦ x·(x|_S)⁻¹`) as morphisms of
  representations;
* `NK.HassePrinciple.projSupported`, `...projOrbitUnits` — the projections of an idèle supported
  on a stable set onto the part supported on a stable subset;
* `NK.HassePrinciple.levelIncl` — the inclusion `𝕀_L^S ⟶ 𝕀_L`.
-/

import Mathlib
import Submission.NK.HassePrinciple.IdeleOrbit
import Submission.NK.HassePrinciple.IdeleOrbitCoind
import Submission.NK.HassePrinciple.RepOfMonoidHom
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace NK.HassePrinciple

open CategoryTheory Representation
open NK.GlobalCFT
open scoped NumberField

/- The generic `ULift.module` instance competes with the module structure stored in a
representation (see `NK.HassePrinciple.injective_h2_units_of_subsingleton_h1_classGroupRep`);
prefer the structure instances, as intended. -/
attribute [local instance 10000] Rep.hV2 Rep.hV1

noncomputable section

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L]

/-! ## Cutting an idèle down to a set of places -/

/-- **The idèle `x` cut down to a set `S` of places**: the idèle with the same components as `x`
on `S` and the components `1` outside `S`. -/
noncomputable def restrictTo (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
    (S : Set (Place L)) (x : Idele L) : Idele L := by
  classical
  refine ⟨fun v => if h : v ∈ S then x v else 1, ?_⟩
  rw [Filter.eventually_cofinite]
  refine (Filter.eventually_cofinite.mp x.2).subset ?_
  intro v hv
  simp only [Set.mem_ofPred_eq] at hv ⊢
  by_cases h : v ∈ S
  · rw [dif_pos h] at hv
    exact hv
  · rw [dif_neg h] at hv
    exact absurd (Subgroup.one_mem (Place.localUnits L v)) hv

theorem restrictTo_apply_of_mem (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
    (S : Set (Place L)) (x : Idele L) {v : Place L} (hv : v ∈ S) :
    restrictTo K L S x v = x v := by
  classical
  rw [show restrictTo K L S x v = (if h : v ∈ S then x v else 1) from rfl, dif_pos hv]

theorem restrictTo_apply_of_not_mem (K L : Type) [Field K] [NumberField K] [Field L]
    [NumberField L] (S : Set (Place L)) (x : Idele L) {v : Place L} (hv : v ∉ S) :
    restrictTo K L S x v = 1 := by
  classical
  rw [show restrictTo K L S x v = (if h : v ∈ S then x v else 1) from rfl, dif_neg hv]

theorem restrictTo_one (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
    (S : Set (Place L)) : restrictTo K L S (1 : Idele L) = 1 := by
  classical
  apply Idele.ext
  intro v
  show (if h : v ∈ S then (1 : Idele L) v else 1) = (1 : (Place.localField L v)ˣ)
  rw [Idele.one_apply]
  by_cases h : v ∈ S
  · rw [dif_pos h]
  · rw [dif_neg h]

theorem restrictTo_mul (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
    (S : Set (Place L)) (x y : Idele L) :
    restrictTo K L S (x * y) = restrictTo K L S x * restrictTo K L S y := by
  classical
  apply Idele.ext
  intro v
  show (if h : v ∈ S then (x * y) v else 1)
    = (if h : v ∈ S then x v else 1) * (if h : v ∈ S then y v else 1)
  rw [Idele.mul_apply]
  by_cases h : v ∈ S
  · rw [dif_pos h, dif_pos h, dif_pos h]
  · rw [dif_neg h, dif_neg h, dif_neg h, one_mul]

theorem restrictTo_mem_supported (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
    (S : Set (Place L)) (x : Idele L) : restrictTo K L S x ∈ supportedSubgroup S := by
  intro v hv
  rw [restrictTo_apply_of_not_mem K L S x hv]

theorem restrictTo_eq_self_of_mem_supported (K L : Type) [Field K] [NumberField K] [Field L]
    [NumberField L] {S : Set (Place L)} {x : Idele L} (hx : x ∈ supportedSubgroup S) :
    restrictTo K L S x = x := by
  classical
  apply Idele.ext
  intro v
  by_cases h : v ∈ S
  · rw [restrictTo_apply_of_mem K L S x h]
  · rw [restrictTo_apply_of_not_mem K L S x h, hx v h]

/-- The action on `𝕀_L` is by group automorphisms: it commutes with the inverse. -/
theorem smul_inv_eq (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] (σ : L ≃ₐ[K] L) (a : Idele L) : (σ • a)⁻¹ = σ • a⁻¹ :=
  ((MulDistribMulAction.toMulAut (L ≃ₐ[K] L) (Idele L) σ).map_inv a).symm

theorem restrictTo_smul (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L]
    (S : Set (Place L)) (hS : ∀ (σ : L ≃ₐ[K] L) ⦃v : Place L⦄, v ∈ S → σ • v ∈ S)
    (σ : L ≃ₐ[K] L) (x : Idele L) :
    restrictTo K L S (σ • x) = σ • restrictTo K L S x := by
  classical
  apply Idele.ext
  intro v
  show (if h : v ∈ S then (σ • x) v else 1)
    = Units.map (Place.localRingEquiv σ⁻¹ v).symm.toMonoidHom
        (if h : σ⁻¹ • v ∈ S then x (σ⁻¹ • v) else 1)
  have hσ : σ⁻¹ • v ∈ S ↔ v ∈ S :=
    ⟨fun h => by have := hS σ h; rwa [smul_inv_smul] at this, fun h => hS σ⁻¹ h⟩
  by_cases h : v ∈ S
  · rw [dif_pos h, dif_pos (hσ.mpr h), Idele.smul_apply]
  · rw [dif_neg h, dif_neg (fun hh => h (hσ.mp hh)), map_one]

/-! ## The complement of a stable set -/

/-- The complement of a `Gal(L/K)`-stable set of places is `Gal(L/K)`-stable. -/
def GStableSet.compl {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L] (S : GStableSet K L) :
    GStableSet K L where
  carrier := S.carrierᶜ
  smul_mem' := by
    intro σ v hv
    rw [Set.mem_compl_iff] at hv ⊢
    intro h
    exact hv (by have := S.smul_mem' σ⁻¹ h; rwa [inv_smul_smul] at this)

@[simp] theorem GStableSet.mem_compl {K L : Type} [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    {S : GStableSet K L} {v : Place L} :
    v ∈ S.compl.carrier ↔ v ∉ S.carrier := Iff.rfl

/-- **The idèles supported outside `S` whose components are local units**
(`∏_{v ∉ S} 𝒪_vˣ`), as a representation of `Gal(L/K)`. -/
noncomputable def outsideUnitsRep (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L] (S : GStableSet K L) :
    Rep.{0, 0, 0} CoeffInt.{0} (L ≃ₐ[K] L) :=
  orbitUnitsRep K L S.compl

/-! ## The projections of the level -/

/-- The projection `𝕀_L^S → A_S = ∏_{v ∈ S} L_vˣ`, the idèle with the same components on `S` and
components `1` outside `S`. -/
noncomputable def levelToSupported (K L : Type) [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L] (S : GStableSet K L) :
    ↥(levelSubgroup S.carrier) →* ↥(supportedSubgroup S.carrier) where
  toFun x := ⟨restrictTo K L S.carrier (x : Idele L),
    restrictTo_mem_supported K L S.carrier (x : Idele L)⟩
  map_one' := Subtype.ext (restrictTo_one K L S.carrier)
  map_mul' x y := Subtype.ext (restrictTo_mul K L S.carrier (x : Idele L) (y : Idele L))

theorem levelToSupported_smul (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L] (S : GStableSet K L)
    (σ : L ≃ₐ[K] L) (x : ↥(levelSubgroup S.carrier)) :
    levelToSupported K L S (σ • x) = σ • levelToSupported K L S x :=
  Subtype.ext (restrictTo_smul K L S.carrier S.smul_mem' σ (x : Idele L))

/-- **The projection `𝕀_L^S ⟶ ∏_{v ∈ S} L_vˣ`**, as a morphism of representations. -/
noncomputable def levelToSupportedHom (K L : Type) [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L] (S : GStableSet K L) :
    levelRep K L S ⟶ supportedRep K L S :=
  repHomOfMonoidHom (levelToSupported K L S) (levelToSupported_smul K L S)

/-- The idèle `x · (x|_S)⁻¹` for `x ∈ 𝕀_L^S`: it is supported outside `S` and all its components
are local units. -/
theorem mem_mul_inv_restrictTo (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L] {S : GStableSet K L} {x : Idele L}
    (hx : x ∈ levelSubgroup S.carrier) :
    x * (restrictTo K L S.carrier x)⁻¹ ∈ orbitUnitsSubgroup (K := K) S.compl.carrier := by
  classical
  rw [mem_orbitUnitsSubgroup]
  constructor
  · intro v hv
    have hv' : v ∈ S.carrier := by simpa using hv
    rw [Idele.mul_apply, Idele.inv_apply, restrictTo_apply_of_mem K L S.carrier x hv',
      mul_inv_cancel]
  · intro v
    by_cases hv : v ∈ S.carrier
    · rw [Idele.mul_apply, Idele.inv_apply, restrictTo_apply_of_mem K L S.carrier x hv,
        mul_inv_cancel]
      exact Subgroup.one_mem _
    · rw [Idele.mul_apply, Idele.inv_apply, restrictTo_apply_of_not_mem K L S.carrier x hv,
        inv_one, mul_one]
      exact (mem_levelSubgroup.mp hx v (by simpa using hv))

/-- The projection `𝕀_L^S → ∏_{v ∉ S} 𝒪_vˣ`, the idèle `x · (x|_S)⁻¹`. -/
noncomputable def levelToOutside (K L : Type) [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L] (S : GStableSet K L) :
    ↥(levelSubgroup S.carrier) →* ↥(orbitUnitsSubgroup (K := K) S.compl.carrier) where
  toFun x := ⟨(x : Idele L) * (restrictTo K L S.carrier (x : Idele L))⁻¹,
    mem_mul_inv_restrictTo K L x.2⟩
  map_one' := Subtype.ext (by
    show (1 : Idele L) * (restrictTo K L S.carrier (1 : Idele L))⁻¹ = (1 : Idele L)
    rw [restrictTo_one K L S.carrier, inv_one, mul_one])
  map_mul' x y := Subtype.ext (by
    show ((x : Idele L) * (y : Idele L))
        * (restrictTo K L S.carrier ((x : Idele L) * (y : Idele L)))⁻¹
      = ((x : Idele L) * (restrictTo K L S.carrier (x : Idele L))⁻¹)
        * ((y : Idele L) * (restrictTo K L S.carrier (y : Idele L))⁻¹)
    rw [restrictTo_mul K L S.carrier, mul_inv]
    ac_rfl)

theorem levelToOutside_smul (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L] (S : GStableSet K L)
    (σ : L ≃ₐ[K] L) (x : ↥(levelSubgroup S.carrier)) :
    levelToOutside K L S (σ • x) = σ • levelToOutside K L S x := by
  apply Subtype.ext
  show ((σ • x : ↥(levelSubgroup S.carrier)) : Idele L)
      * (restrictTo K L S.carrier ((σ • x : ↥(levelSubgroup S.carrier)) : Idele L))⁻¹
    = σ • ((levelToOutside K L S x : ↥(orbitUnitsSubgroup (K := K) S.compl.carrier)) : Idele L)
  rw [show ((σ • x : ↥(levelSubgroup S.carrier)) : Idele L) = σ • (x : Idele L) from rfl]
  rw [show ((levelToOutside K L S x : ↥(orbitUnitsSubgroup (K := K) S.compl.carrier)) : Idele L)
      = (x : Idele L) * (restrictTo K L S.carrier (x : Idele L))⁻¹ from rfl]
  rw [restrictTo_smul K L S.carrier S.smul_mem']
  rw [show σ • ((x : Idele L) * (restrictTo K L S.carrier (x : Idele L))⁻¹)
      = (σ • (x : Idele L)) * (σ • (restrictTo K L S.carrier (x : Idele L)))⁻¹ from by
        rw [MulDistribMulAction.smul_mul, smul_inv_eq K L σ]]

/-- **The projection `𝕀_L^S ⟶ ∏_{v ∉ S} 𝒪_vˣ`**, as a morphism of representations. -/
noncomputable def levelToOutsideHom (K L : Type) [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L] (S : GStableSet K L) :
    levelRep K L S ⟶ outsideUnitsRep K L S :=
  repHomOfMonoidHom (levelToOutside K L S) (levelToOutside_smul K L S)

/-! ## The inclusion of a level into the idèles -/

/-- **The inclusion `𝕀_L^S ⟶ 𝕀_L`**, as a morphism of representations. -/
noncomputable def levelIncl (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L] (S : GStableSet K L) :
    levelRep K L S ⟶ ideleRep K L :=
  repHomOfMonoidHom (Subgroup.subtype (levelSubgroup S.carrier)) (fun _ _ => rfl)

/-! ## Projections onto stable subsets -/

/-- The projection `∏_{v ∈ S} L_vˣ ⟶ ∏_{v ∈ O} L_vˣ` for stable sets `O ⊆ S`. -/
noncomputable def projSupported (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L] (S O : GStableSet K L) :
    ↥(supportedSubgroup S.carrier) →* ↥(supportedSubgroup O.carrier) where
  toFun x := ⟨restrictTo K L O.carrier (x : Idele L),
    restrictTo_mem_supported K L O.carrier (x : Idele L)⟩
  map_one' := Subtype.ext (restrictTo_one K L O.carrier)
  map_mul' x y := Subtype.ext (restrictTo_mul K L O.carrier (x : Idele L) (y : Idele L))

theorem projSupported_smul (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L] (S O : GStableSet K L)
    (σ : L ≃ₐ[K] L) (x : ↥(supportedSubgroup S.carrier)) :
    projSupported K L S O (σ • x) = σ • projSupported K L S O x :=
  Subtype.ext (restrictTo_smul K L O.carrier O.smul_mem' σ (x : Idele L))

/-- **The projection `∏_{v ∈ S} L_vˣ ⟶ ∏_{v ∈ O} L_vˣ`** (`O ⊆ S`), as a morphism of
representations. -/
noncomputable def projSupportedHom (K L : Type) [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (S O : GStableSet K L) : supportedRep K L S ⟶ supportedRep K L O :=
  repHomOfMonoidHom (projSupported K L S O) (projSupported_smul K L S O)

/-- The projection `∏_{v ∉ S} 𝒪_vˣ ⟶ ∏_{v ∈ O} 𝒪_vˣ` for stable sets `O`. -/
noncomputable def projOrbitUnits (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L] (S O : GStableSet K L) :
    ↥(orbitUnitsSubgroup (K := K) S.compl.carrier) →*
      ↥(orbitUnitsSubgroup (K := K) O.carrier) where
  toFun x := ⟨restrictTo K L O.carrier (x : Idele L), by
    rw [mem_orbitUnitsSubgroup]
    constructor
    · intro v hv
      rw [restrictTo_apply_of_not_mem K L O.carrier (x : Idele L) hv]
    · intro v
      by_cases hv : v ∈ O.carrier
      · rw [restrictTo_apply_of_mem K L O.carrier (x : Idele L) hv]
        exact (mem_unitySubgroup.mp (Subgroup.mem_inf.mp x.2).2) v
      · rw [restrictTo_apply_of_not_mem K L O.carrier (x : Idele L) hv]
        exact Subgroup.one_mem _⟩
  map_one' := Subtype.ext (restrictTo_one K L O.carrier)
  map_mul' x y := Subtype.ext (restrictTo_mul K L O.carrier (x : Idele L) (y : Idele L))

theorem projOrbitUnits_smul (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L] (S O : GStableSet K L)
    (σ : L ≃ₐ[K] L) (x : ↥(orbitUnitsSubgroup (K := K) S.compl.carrier)) :
    projOrbitUnits K L S O (σ • x) = σ • projOrbitUnits K L S O x :=
  Subtype.ext (restrictTo_smul K L O.carrier O.smul_mem' σ (x : Idele L))

/-- **The projection `∏_{v ∉ S} 𝒪_vˣ ⟶ ∏_{v ∈ O} 𝒪_vˣ`**, as a morphism of representations. -/
noncomputable def projOrbitUnitsHom (K L : Type) [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (S O : GStableSet K L) :
    outsideUnitsRep K L S ⟶ orbitUnitsRep K L O :=
  repHomOfMonoidHom (projOrbitUnits K L S O) (projOrbitUnits_smul K L S O)

/-! ## Inclusions of the two summands of a level -/

/-- The idèles supported on `S` are idèles of the level `𝕀_L^S`. -/
theorem supportedSubgroup_le_level (K L : Type) [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] {S : GStableSet K L} :
    supportedSubgroup S.carrier ≤ levelSubgroup S.carrier := by
  intro x hx v hv
  rw [hx v hv]
  exact Subgroup.one_mem _

/-- The idèles supported outside `S` with local-unit components are idèles of the level
`𝕀_L^S`. -/
theorem orbitUnitsSubgroup_le_level (K L : Type) [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L] {S : GStableSet K L} :
    orbitUnitsSubgroup (K := K) S.compl.carrier ≤ levelSubgroup S.carrier := by
  intro x hx v _
  exact (mem_orbitUnitsSubgroup.mp hx).2 v

/-- **The inclusion `∏_{v ∈ S} L_vˣ ⟶ 𝕀_L^S`**, as a morphism of representations. -/
noncomputable def inclSupported (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L] (S : GStableSet K L) :
    supportedRep K L S ⟶ levelRep K L S :=
  repHomOfMonoidHom (Subgroup.inclusion (supportedSubgroup_le_level K L (S := S)))
    (fun _ _ => rfl)

/-- **The inclusion `∏_{v ∉ S} 𝒪_vˣ ⟶ 𝕀_L^S`**, as a morphism of representations. -/
noncomputable def inclOutsideUnits (K L : Type) [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L] (S : GStableSet K L) :
    outsideUnitsRep K L S ⟶ levelRep K L S :=
  repHomOfMonoidHom (Subgroup.inclusion (orbitUnitsSubgroup_le_level K L (S := S)))
    (fun _ _ => rfl)

theorem inclSupported_comp (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L] (S : GStableSet K L) :
    inclSupported K L S ≫ levelToSupportedHom K L S = 𝟙 (supportedRep K L S) := by
  have h : ∀ y : ↥(supportedSubgroup S.carrier),
      (levelToSupported K L S)
        (Subgroup.inclusion (supportedSubgroup_le_level K L (S := S)) y) = y := by
    intro y
    apply Subtype.ext
    show restrictTo K L S.carrier (↑y) = ↑y
    rw [restrictTo_eq_self_of_mem_supported K L y.2]
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro x
  show (levelToSupported K L S)
      ((Subgroup.inclusion (supportedSubgroup_le_level K L (S := S))) (Additive.toMul x))
    = Additive.toMul x
  rw [h (Additive.toMul x)]
  rfl

theorem inclOutsideUnits_comp (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L] (S : GStableSet K L) :
    inclOutsideUnits K L S ≫ levelToOutsideHom K L S = 𝟙 (outsideUnitsRep K L S) := by
  have h : ∀ y : ↥(orbitUnitsSubgroup (K := K) S.compl.carrier),
      (levelToOutside K L S)
        (Subgroup.inclusion (orbitUnitsSubgroup_le_level K L (S := S)) y) = y := by
    intro y
    apply Subtype.ext
    show ((y : ↥(orbitUnitsSubgroup (K := K) S.compl.carrier)) : Idele L)
        * (restrictTo K L S.carrier
            (((y : ↥(orbitUnitsSubgroup (K := K) S.compl.carrier)) : Idele L)))⁻¹
      = ((y : ↥(orbitUnitsSubgroup (K := K) S.compl.carrier)) : Idele L)
    rw [show restrictTo K L S.carrier
        (((y : ↥(orbitUnitsSubgroup (K := K) S.compl.carrier)) : Idele L)) = 1 from by
      apply Idele.ext
      intro v
      by_cases hv : v ∈ S.carrier
      · rw [restrictTo_apply_of_mem K L S.carrier _ hv,
          (mem_orbitUnitsSubgroup.mp y.2).1 v (by simpa using hv)]
        rfl
      · rw [restrictTo_apply_of_not_mem K L S.carrier _ hv, Idele.one_apply]]
    rw [inv_one, mul_one]
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro x
  show (levelToOutside K L S)
      ((Subgroup.inclusion (orbitUnitsSubgroup_le_level K L (S := S))) (Additive.toMul x))
    = Additive.toMul x
  rw [h (Additive.toMul x)]
  rfl

/-! ## The lift maps of the orbit decompositions -/

open NK.RepresentationTheory.GroupCohomology in
/-- The orbits contained in a stable set `S`. -/
abbrev orbitIndexIn (S : GStableSet K L) :=
  {O : GStableSet K L // O.carrier ⊆ S.carrier ∧ IsOrbit K L O.carrier}

open NK.RepresentationTheory.GroupCohomology in
/-- The orbits disjoint from a stable set `S`. -/
abbrev orbitIndexOut (S : GStableSet K L) :=
  {O : GStableSet K L // IsOrbit K L O.carrier ∧ Disjoint O.carrier S.carrier}

/-- **The lift `∏_{v ∈ S} L_vˣ ⟶ ∏_{O ⊆ S} (∏_{v ∈ O} L_vˣ)`** used to reduce a class on a level
to its orbit components. -/
noncomputable def supportedLift (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L] (S : GStableSet K L) :
    supportedRep K L S ⟶
      NK.RepresentationTheory.GroupCohomology.piRep
        (fun O : orbitIndexIn (K := K) (L := L) S => supportedRep K L O.1) :=
  Rep.ofHom
    { toFun := fun x O => (projSupportedHom K L S O.1).hom x
      map_add' := fun x y => by
        funext O
        exact map_add (projSupportedHom K L S O.1).hom x y
      map_smul' := fun n x => by
        funext O
        exact map_smul (projSupportedHom K L S O.1).hom n x
      isIntertwining' := fun σ => by
        apply LinearMap.ext
        intro x
        funext O
        exact Rep.hom_comm_apply (projSupportedHom K L S O.1) σ x }

/-- **The lift `∏_{v ∉ S} 𝒪_vˣ ⟶ ∏_{O ∩ S = ∅} (∏_{v ∈ O} 𝒪_vˣ)`** used to reduce a class on a
level to its orbit components. -/
noncomputable def outsideUnitsLift (K L : Type) [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L] (S : GStableSet K L) :
    outsideUnitsRep K L S ⟶
      NK.RepresentationTheory.GroupCohomology.piRep
        (fun O : orbitIndexOut (K := K) (L := L) S => orbitUnitsRep K L O.1) :=
  Rep.ofHom
    { toFun := fun x O => (projOrbitUnitsHom K L S O.1).hom x
      map_add' := fun x y => by
        funext O
        exact map_add (projOrbitUnitsHom K L S O.1).hom x y
      map_smul' := fun n x => by
        funext O
        exact map_smul (projOrbitUnitsHom K L S O.1).hom n x
      isIntertwining' := fun σ => by
        apply LinearMap.ext
        intro x
        funext O
        exact Rep.hom_comm_apply (projOrbitUnitsHom K L S O.1) σ x }

end

end NK.HassePrinciple
