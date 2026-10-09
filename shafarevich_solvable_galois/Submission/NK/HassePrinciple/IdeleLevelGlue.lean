/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The glue between the localisation at a place and the coinduced model

* `NK.HassePrinciple.res_coindToHom_counit` — the triangle identity of the
  restriction–coinduction adjunction: restricting the adjunction transpose of a `Γ_w`-map to `Γ_w`
  and composing with the counit gives back the map;
* `NK.HassePrinciple.res_levelIncl_comp_A`, `..._U` — the factorisation of "evaluate at `w`"
  along the level inclusion through the two projections of the level and the coordinate at `w`.
-/

import Mathlib
import Submission.NK.HassePrinciple.IdeleLevel
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1600000
set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace NK.HassePrinciple

open CategoryTheory Representation
open NK.GlobalCFT
open scoped NumberField

noncomputable section

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L]

attribute [local instance 10000] Rep.hV2 Rep.hV1

/-! ## The triangle identity of the restriction–coinduction adjunction -/

theorem res_coindToHom_counit (w : Place L) (M : Rep.{0,0,0} CoeffInt.{0} (L ≃ₐ[K] L))
    (A : Rep.{0,0,0} CoeffInt.{0} (MulAction.stabilizer (L ≃ₐ[K] L) w))
    (f : Rep.res (MulAction.stabilizer (L ≃ₐ[K] L) w).subtype M ⟶ A) :
    Rep.resMap (MulAction.stabilizer (L ≃ₐ[K] L) w).subtype
        (Rep.resCoindToHom (MulAction.stabilizer (L ≃ₐ[K] L) w).subtype M A f) ≫
      (Rep.resCoindAdjunction CoeffInt (MulAction.stabilizer (L ≃ₐ[K] L) w).subtype).counit.app A
    = f := by
  have h := Adjunction.homEquiv_counit
    (adj := Rep.resCoindAdjunction CoeffInt (MulAction.stabilizer (L ≃ₐ[K] L) w).subtype)
    (X := M) A ((Rep.resCoindHomEquiv (MulAction.stabilizer (L ≃ₐ[K] L) w).subtype M A) f)
  rw [show Rep.resMap (MulAction.stabilizer (L ≃ₐ[K] L) w).subtype
        (Rep.resCoindToHom (MulAction.stabilizer (L ≃ₐ[K] L) w).subtype M A f)
      = (Rep.resFunctor (MulAction.stabilizer (L ≃ₐ[K] L) w).subtype).map
          ((Rep.resCoindHomEquiv (MulAction.stabilizer (L ≃ₐ[K] L) w).subtype M A) f) from rfl]
  rw [← h]
  exact LinearEquiv.symm_apply_apply
    (Rep.resCoindHomEquiv (MulAction.stabilizer (L ≃ₐ[K] L) w).subtype M A) f


/-! ## The factorisation of the localisation at a place of a level -/

theorem res_levelIncl_comp_A (S : GStableSet K L) (w : Place L) (hw : w ∈ S.carrier) :
    Rep.resMap (MulAction.stabilizer (L ≃ₐ[K] L) w).subtype (levelIncl K L S) ≫
        ideleToLocalUnits K L w
      = Rep.resMap (MulAction.stabilizer (L ≃ₐ[K] L) w).subtype (levelToSupportedHom K L S) ≫
        Rep.resMap (MulAction.stabilizer (L ≃ₐ[K] L) w).subtype
          (projSupportedHom K L S (orbitStable K L w)) ≫
        orbitCoordA K L w := by
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro x
  show (ideleToLocalUnits K L w).hom ((levelIncl K L S).hom x)
    = (orbitCoordA K L w).hom ((projSupportedHom K L S (orbitStable K L w)).hom
        ((levelToSupportedHom K L S).hom x))
  rw [show (ideleToLocalUnits K L w).hom ((levelIncl K L S).hom x)
      = Additive.ofMul (((Additive.toMul x : ↥(levelSubgroup S.carrier)) : Idele L) w) from rfl]
  show Additive.ofMul (((Additive.toMul x : ↥(levelSubgroup S.carrier)) : Idele L) w)
      = Additive.ofMul (orbitEvalA K L w (projSupported K L S (orbitStable K L w)
          (levelToSupported K L S (Additive.toMul x))))
  congr 1
  rw [orbitEvalA_apply]
  show ((Additive.toMul x : ↥(levelSubgroup S.carrier)) : Idele L) w
      = ((projSupported K L S (orbitStable K L w)
        (levelToSupported K L S (Additive.toMul x))) : Idele L) w
  rw [show ((projSupported K L S (orbitStable K L w)
        (levelToSupported K L S (Additive.toMul x))) : Idele L)
      = restrictTo K L (placeOrbit K L w)
          (((levelToSupported K L S (Additive.toMul x))) : Idele L) from rfl]
  rw [show (((levelToSupported K L S (Additive.toMul x))) : Idele L)
      = restrictTo K L S.carrier
          (((Additive.toMul x : ↥(levelSubgroup S.carrier)) : Idele L)) from rfl]
  rw [restrictTo_apply_of_mem K L (placeOrbit K L w) _
    (mem_placeOrbit.mpr ⟨1, by rw [one_smul]⟩)]
  rw [restrictTo_apply_of_mem K L S.carrier _ hw]

theorem res_levelIncl_comp_U (S : GStableSet K L) (w : Place L) (hw : w ∉ S.carrier) :
    Rep.resMap (MulAction.stabilizer (L ≃ₐ[K] L) w).subtype (levelIncl K L S) ≫
        ideleToLocalUnits K L w
      = Rep.resMap (MulAction.stabilizer (L ≃ₐ[K] L) w).subtype (levelToOutsideHom K L S) ≫
        Rep.resMap (MulAction.stabilizer (L ≃ₐ[K] L) w).subtype
          (projOrbitUnitsHom K L S (orbitStable K L w)) ≫
        orbitCoordU K L w ≫ localUnitsIncl w := by
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro x
  show (ideleToLocalUnits K L w).hom ((levelIncl K L S).hom x)
    = (localUnitsIncl w).hom ((orbitCoordU K L w).hom
        ((projOrbitUnitsHom K L S (orbitStable K L w)).hom ((levelToOutsideHom K L S).hom x)))
  rw [show (ideleToLocalUnits K L w).hom ((levelIncl K L S).hom x)
      = Additive.ofMul (((Additive.toMul x : ↥(levelSubgroup S.carrier)) : Idele L) w) from rfl]
  show Additive.ofMul (((Additive.toMul x : ↥(levelSubgroup S.carrier)) : Idele L) w)
      = Additive.ofMul ((orbitEvalU K L w (projOrbitUnits K L S (orbitStable K L w)
          (levelToOutside K L S (Additive.toMul x))) : ↥(Place.localUnits L w)) :
            (Place.localField L w)ˣ)
  congr 1
  rw [orbitEvalU_apply]
  show ((Additive.toMul x : ↥(levelSubgroup S.carrier)) : Idele L) w
      = ((projOrbitUnits K L S (orbitStable K L w)
        (levelToOutside K L S (Additive.toMul x))) : Idele L) w
  rw [show ((projOrbitUnits K L S (orbitStable K L w)
        (levelToOutside K L S (Additive.toMul x))) : Idele L)
      = restrictTo K L (placeOrbit K L w)
          (((levelToOutside K L S (Additive.toMul x))) : Idele L) from rfl]
  rw [show (((levelToOutside K L S (Additive.toMul x))) : Idele L)
      = ((Additive.toMul x : ↥(levelSubgroup S.carrier)) : Idele L)
        * (restrictTo K L S.carrier
            (((Additive.toMul x : ↥(levelSubgroup S.carrier)) : Idele L)))⁻¹ from rfl]
  rw [restrictTo_apply_of_mem K L (placeOrbit K L w) _
    (mem_placeOrbit.mpr ⟨1, by rw [one_smul]⟩)]
  rw [Idele.mul_apply, Idele.inv_apply, restrictTo_apply_of_not_mem K L S.carrier _ hw,
    inv_one, mul_one]


/-! ## The localisation identity -/

end

end NK.HassePrinciple
