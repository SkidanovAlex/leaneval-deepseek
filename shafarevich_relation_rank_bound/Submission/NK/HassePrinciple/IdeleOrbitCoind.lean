/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The orbit of a place and its coinduced model

This module carries out the *geometric* step of `NK.HassePrinciple.hbnIdele`: the idèles
supported on the `Gal(L/K)`-orbit of a place `w`, and those supported there with local-unit
components, are the coinduced modules `Coind_{Γ_w}^{Γ}(L_wˣ)` and `Coind_{Γ_w}^{Γ}(𝒪_wˣ)`
(`Γ_w = MulAction.stabilizer (L ≃ₐ[K] L) w`).

* `NK.HassePrinciple.orbitStable` — the orbit of `w` as a `Gal(L/K)`-stable set of places;
* `NK.HassePrinciple.orbitEvalA`, `...orbitEvalU` — the "coordinate at `w`" of an idèle
  supported on the orbit, as a monoid homomorphism;
* `NK.HassePrinciple.orbitCoordA`, `...orbitCoordU` — the same coordinate as a map of
  `Γ_w`-representations;
* `NK.HassePrinciple.orbitCoindMapA`, `...orbitCoindMapU` — its adjunction transpose, a map of
  `Γ`-representations into the coinduced module.  It is the map whose composition with Shapiro's
  isomorphism `groupCohomology.coindIso` is the localisation at `w`.
-/

import Mathlib
import Submission.NK.HassePrinciple.IdeleOrbit
import Submission.NK.HassePrinciple.LocalUnitsSub

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace NK.HassePrinciple

open CategoryTheory Representation
open NK.GlobalCFT
open scoped NumberField

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L]

/-! ## The orbit of a place -/

/-- **The `Gal(L/K)`-orbit of a place**, as a `Gal(L/K)`-stable set of places. -/
def orbitStable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L] (w : Place L) : GStableSet K L where
  carrier := placeOrbit K L w
  smul_mem' := fun σ _ hv => orbit_smul_mem w σ hv

/-- A set of places that is the `Gal(L/K)`-orbit of some place. -/
def IsOrbit (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L] (O : Set (Place L)) : Prop :=
  ∃ w : Place L, O = placeOrbit K L w

theorem isOrbit_orbitStable (w : Place L) : IsOrbit K L (orbitStable K L w).carrier :=
  ⟨w, rfl⟩

/-- The action of `Γ` on the idèles supported on a stable set. -/
@[simp] theorem supportedRep_ρ_apply (O : GStableSet K L) (g : L ≃ₐ[K] L)
    (x : (supportedRep K L O).V) :
    (supportedRep K L O).ρ g x =
      Additive.ofMul (g • (Additive.toMul x : ↥(supportedSubgroup O.carrier))) := by
  change (Rep.ofDistribMulAction CoeffInt (L ≃ₐ[K] L)
    (Additive ↥(supportedSubgroup O.carrier))).ρ g x = _
  rw [Rep.ofDistribMulAction_ρ_apply_apply]
  rfl

/-- The action of `Γ` on the idèles supported on a stable set with local-unit components. -/
@[simp] theorem orbitUnitsRep_ρ_apply (O : GStableSet K L) (g : L ≃ₐ[K] L)
    (x : (orbitUnitsRep K L O).V) :
    (orbitUnitsRep K L O).ρ g x =
      Additive.ofMul (g • (Additive.toMul x : ↥(orbitUnitsSubgroup (K := K) O.carrier))) := by
  change (Rep.ofDistribMulAction CoeffInt (L ≃ₐ[K] L)
    (Additive ↥(orbitUnitsSubgroup (K := K) O.carrier))).ρ g x = _
  rw [Rep.ofDistribMulAction_ρ_apply_apply]
  rfl

/-- The action of `Γ_w` on the local units, in the form used by the coinduced module. -/
@[simp] theorem localUnitsSubRep_ρ_apply (w : Place L)
    (σ : MulAction.stabilizer (L ≃ₐ[K] L) w) (u : (localUnitsSubRep K L w).V) :
    (localUnitsSubRep K L w).ρ σ u =
      Additive.ofMul (σ • (Additive.toMul u : ↥(Place.localUnits L w))) := by
  change (Rep.ofDistribMulAction CoeffInt
    (MulAction.stabilizer (L ≃ₐ[K] L) w) (Additive ↥(Place.localUnits L w))).ρ σ u = _
  rw [Rep.ofDistribMulAction_ρ_apply_apply]
  rfl

/-! ## The coordinate at `w` -/

/-- The `w`-component of an idèle supported on the orbit of `w`. -/
noncomputable def orbitEvalA (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L] (w : Place L) :
    ↥(supportedSubgroup (placeOrbit K L w)) →* (Place.localField L w)ˣ :=
  (Idele.eval w).comp (Subgroup.subtype (supportedSubgroup (placeOrbit K L w)))

/-- The `w`-component of an idèle supported on the orbit of `w` whose components are local
units. -/
noncomputable def orbitEvalU (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L] (w : Place L) :
    ↥(orbitUnitsSubgroup (K := K) (placeOrbit K L w)) →* ↥(Place.localUnits L w) where
  toFun x := ⟨((x : Idele L)) w,
    (mem_unitySubgroup.mp (Subgroup.mem_inf.mp x.2).2) w⟩
  map_one' := Subtype.ext (Idele.one_apply w)
  map_mul' x y := Subtype.ext (Idele.mul_apply (x : Idele L) (y : Idele L) w)

theorem orbitEvalA_smul (w : Place L) (σ : MulAction.stabilizer (L ≃ₐ[K] L) w)
    (x : ↥(supportedSubgroup (placeOrbit K L w))) :
    orbitEvalA K L w (σ.1 • x) = localUnitsEquiv (K := K) w σ (orbitEvalA K L w x) := by
  rw [show orbitEvalA K L w (σ.1 • x)
      = ((σ.1 • x : ↥(supportedSubgroup (placeOrbit K L w))) : Idele L) w from rfl]
  rw [show ((σ.1 • x : ↥(supportedSubgroup (placeOrbit K L w))) : Idele L)
      = σ.1 • (x : Idele L) from rfl]
  rw [smul_apply_stabilizer]
  rw [show orbitEvalA K L w x = ((x : Idele L)) w from rfl]
  rfl

theorem orbitEvalU_smul (w : Place L) (σ : MulAction.stabilizer (L ≃ₐ[K] L) w)
    (x : ↥(orbitUnitsSubgroup (K := K) (placeOrbit K L w))) :
    orbitEvalU K L w (σ.1 • x) = σ • orbitEvalU K L w x := by
  apply Subtype.ext
  rw [show (orbitEvalU K L w (σ.1 • x) : (Place.localField L w)ˣ)
      = ((σ.1 • x : ↥(orbitUnitsSubgroup (K := K) (placeOrbit K L w))) : Idele L) w from rfl]
  rw [show ((σ.1 • x : ↥(orbitUnitsSubgroup (K := K) (placeOrbit K L w))) : Idele L)
      = σ.1 • (x : Idele L) from rfl]
  rw [show ((σ • orbitEvalU K L w x : ↥(Place.localUnits L w)) : (Place.localField L w)ˣ)
      = localUnitsEquiv (K := K) w σ (orbitEvalU K L w x) from rfl]
  rw [smul_apply_stabilizer]
  rw [show (orbitEvalU K L w x : (Place.localField L w)ˣ) = ((x : Idele L)) w from rfl]
  rfl

@[simp] theorem orbitEvalA_apply (w : Place L) (x : ↥(supportedSubgroup (placeOrbit K L w))) :
    orbitEvalA K L w x = ((x : Idele L)) w := rfl

@[simp] theorem orbitEvalU_apply (w : Place L)
    (x : ↥(orbitUnitsSubgroup (K := K) (placeOrbit K L w))) :
    (orbitEvalU K L w x : (Place.localField L w)ˣ) = ((x : Idele L)) w := rfl

/-- **The coordinate at `w` of an idèle supported on the orbit of `w`**, as a morphism of
`Γ_w`-representations `A_O → L_wˣ` (`O = Gal(L/K)·w`). -/
noncomputable def orbitCoordA (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L] (w : Place L) :
    Rep.res.{0, 0, 0, 0} (MulAction.stabilizer (L ≃ₐ[K] L) w).subtype
        (supportedRep K L (orbitStable K L w)) ⟶ localUnitsRep K L w :=
  Rep.ofHom
    { toFun := fun x => Additive.ofMul
        (orbitEvalA K L w (Additive.toMul x : ↥(supportedSubgroup (placeOrbit K L w))))
      map_add' := fun x y => by
        show Additive.ofMul (orbitEvalA K L w (Additive.toMul (x + y) :
              ↥(supportedSubgroup (placeOrbit K L w))))
          = Additive.ofMul (orbitEvalA K L w (Additive.toMul x :
              ↥(supportedSubgroup (placeOrbit K L w))))
            + Additive.ofMul (orbitEvalA K L w (Additive.toMul y :
              ↥(supportedSubgroup (placeOrbit K L w))))
        rw [toMul_add, map_mul, ofMul_mul]
      map_smul' := fun n x => by
        obtain ⟨z⟩ := n
        show Additive.ofMul (orbitEvalA K L w (Additive.toMul (z • x) :
              ↥(supportedSubgroup (placeOrbit K L w))))
          = z • Additive.ofMul (orbitEvalA K L w (Additive.toMul x :
              ↥(supportedSubgroup (placeOrbit K L w))))
        rw [toMul_zsmul, map_zpow, ofMul_zpow]
      isIntertwining' := fun σ => by
        apply LinearMap.ext
        intro x
        show Additive.ofMul (orbitEvalA K L w (Additive.toMul
              ((Rep.res (MulAction.stabilizer (L ≃ₐ[K] L) w).subtype
                (supportedRep K L (orbitStable K L w))).ρ σ x) :
                ↥(supportedSubgroup (placeOrbit K L w))))
          = Additive.ofMul (localUnitsEquiv (K := K) w σ
              (orbitEvalA K L w (Additive.toMul x :
                ↥(supportedSubgroup (placeOrbit K L w)))))
        change Additive.ofMul (orbitEvalA K L w (Additive.toMul
              ((supportedRep K L (orbitStable K L w)).ρ σ.1 x) :
                ↥(supportedSubgroup (placeOrbit K L w))))
          = Additive.ofMul (localUnitsEquiv (K := K) w σ
              (orbitEvalA K L w (Additive.toMul x :
                ↥(supportedSubgroup (placeOrbit K L w)))))
        rw [supportedRep_ρ_apply]
        show Additive.ofMul (orbitEvalA K L w (σ.1 • (Additive.toMul x :
              ↥(supportedSubgroup (placeOrbit K L w)))))
          = Additive.ofMul (localUnitsEquiv (K := K) w σ
              (orbitEvalA K L w (Additive.toMul x :
                ↥(supportedSubgroup (placeOrbit K L w)))))
        rw [orbitEvalA_smul] }

/-- **The coordinate at `w` of an idèle supported on the orbit of `w` with local-unit
components**, as a morphism of `Γ_w`-representations `U_O → 𝒪_wˣ`. -/
noncomputable def orbitCoordU (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L] (w : Place L) :
    Rep.res.{0, 0, 0, 0} (MulAction.stabilizer (L ≃ₐ[K] L) w).subtype
        (orbitUnitsRep K L (orbitStable K L w)) ⟶ localUnitsSubRep K L w :=
  Rep.ofHom
    { toFun := fun x => Additive.ofMul
        (orbitEvalU K L w (Additive.toMul x :
          ↥(orbitUnitsSubgroup (K := K) (placeOrbit K L w))))
      map_add' := fun x y => by
        show Additive.ofMul (orbitEvalU K L w (Additive.toMul (x + y) :
              ↥(orbitUnitsSubgroup (K := K) (placeOrbit K L w))))
          = Additive.ofMul (orbitEvalU K L w (Additive.toMul x :
              ↥(orbitUnitsSubgroup (K := K) (placeOrbit K L w))))
            + Additive.ofMul (orbitEvalU K L w (Additive.toMul y :
              ↥(orbitUnitsSubgroup (K := K) (placeOrbit K L w))))
        rw [toMul_add, map_mul, ofMul_mul]
      map_smul' := fun n x => by
        obtain ⟨z⟩ := n
        show Additive.ofMul (orbitEvalU K L w (Additive.toMul (z • x) :
              ↥(orbitUnitsSubgroup (K := K) (placeOrbit K L w))))
          = z • Additive.ofMul (orbitEvalU K L w (Additive.toMul x :
              ↥(orbitUnitsSubgroup (K := K) (placeOrbit K L w))))
        rw [toMul_zsmul, map_zpow, ofMul_zpow]
      isIntertwining' := fun σ => by
        apply LinearMap.ext
        intro x
        show Additive.ofMul (orbitEvalU K L w (Additive.toMul
              ((Rep.res (MulAction.stabilizer (L ≃ₐ[K] L) w).subtype
                (orbitUnitsRep K L (orbitStable K L w))).ρ σ x) :
                ↥(orbitUnitsSubgroup (K := K) (placeOrbit K L w))))
          = Additive.ofMul (σ • (orbitEvalU K L w (Additive.toMul x :
                ↥(orbitUnitsSubgroup (K := K) (placeOrbit K L w))) :
                ↥(Place.localUnits L w)))
        change Additive.ofMul (orbitEvalU K L w (Additive.toMul
              ((orbitUnitsRep K L (orbitStable K L w)).ρ σ.1 x) :
                ↥(orbitUnitsSubgroup (K := K) (placeOrbit K L w))))
          = Additive.ofMul (σ • (orbitEvalU K L w (Additive.toMul x :
                ↥(orbitUnitsSubgroup (K := K) (placeOrbit K L w))) :
                ↥(Place.localUnits L w)))
        rw [orbitUnitsRep_ρ_apply]
        show Additive.ofMul (orbitEvalU K L w (σ.1 • (Additive.toMul x :
              ↥(orbitUnitsSubgroup (K := K) (placeOrbit K L w)))))
          = Additive.ofMul (σ • (orbitEvalU K L w (Additive.toMul x :
                ↥(orbitUnitsSubgroup (K := K) (placeOrbit K L w))) :
                ↥(Place.localUnits L w)))
        rw [orbitEvalU_smul] }

/-! ## The maps into the coinduced modules -/

/-- **The `Γ`-map `A_O ⟶ Coind_{Γ_w}^{Γ} L_wˣ`** (`O = Gal(L/K)·w`), the adjunction transpose of
the coordinate at `w`.  Composed with Shapiro's isomorphism `groupCohomology.coindIso` it is the
localisation at `w`. -/
noncomputable def orbitCoindMapA (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L] (w : Place L) :
    supportedRep K L (orbitStable K L w) ⟶
      Rep.coind (MulAction.stabilizer (L ≃ₐ[K] L) w).subtype (localUnitsRep K L w) :=
  Rep.resCoindToHom _ _ _ (orbitCoordA K L w)

/-- **The `Γ`-map `U_O ⟶ Coind_{Γ_w}^{Γ} 𝒪_wˣ`**, the adjunction transpose of the coordinate
at `w`. -/
noncomputable def orbitCoindMapU (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L] (w : Place L) :
    orbitUnitsRep K L (orbitStable K L w) ⟶
      Rep.coind (MulAction.stabilizer (L ≃ₐ[K] L) w).subtype (localUnitsSubRep K L w) :=
  Rep.resCoindToHom _ _ _ (orbitCoordU K L w)

end

end NK.HassePrinciple
