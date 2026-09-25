/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Equivariance of the units inclusion under the restriction action

Umbrella development: `Submission/Work/HassePrinciple/` (README §8.4 item 1, §10.4).

For a level inclusion `L ≤ L'` of finite Galois intermediate fields of `K'/K`, the unit inclusion
`unitsInclLinearMap L L' h : Additive (↥L)ˣ →ₗ[CoeffInt] Additive (↥L')ˣ` (the `CoeffInt`-linear
form of `Lˣ ↪ L'ˣ`, `Submission/Work/HassePrinciple/UnitsLevel.lean`) is **equivariant** for the
actions of `Gal(K'/K)` on the two levels, given by restriction along
`levelRestrict L : Gal(K'/K) →* Gal(↥L/K)`:

`unitsInclLinearMap L L' h ((levelRestrict L σ) • x) =
  (levelRestrict L' σ) • unitsInclLinearMap L L' h x`   for `σ : Gal(K'/K)`, `x : Additive (↥L)ˣ`.

Both sides are `Additive`-wrapped units of `L'`, and both have underlying element `σ (↑x)` in `K'`:
the restriction `levelRestrict L σ` acts on `↥L` as `σ` does on `K'` (`AlgEquiv.restrictNormalHom_apply`)
and the inclusion `↥L ↪ ↥L'` is the identity on underlying elements of `K'`
(`IntermediateField.coe_inclusion`).

This is the equivariance needed to build the coefficient morphism
`unitsLevelMapCoeff h : Rep.res (levelQuotHom h) (unitsLevelRep V L) ⟶ unitsLevelRep V L'`
of the units level system, exactly as `NK.BrauerTwist.muIncl_smul` is used for `μ_p`; see the
module docstring of `Submission/Work/HassePrinciple/UnitsLevel.lean`.
-/
import Mathlib
import Submission.NK.HassePrinciple.UnitsLevel
import Submission.NK.HassePrinciple.LevelDictionary

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 400000

universe u

namespace NK.HassePrinciple

theorem unitsIncl_smul {K K' : Type u} [Field K] [Field K'] [Algebra K K'] [IsSepClosure K K']
    (L L' : FiniteGaloisIntermediateField K K') (h : L ≤ L') (σ : K' ≃ₐ[K] K')
    (x : Additive (↥L)ˣ) :
    NK.HassePrinciple.unitsInclLinearMap L L' h
        ((NK.HassePrinciple.levelRestrict L σ) • x) =
      (NK.HassePrinciple.levelRestrict L' σ) • NK.HassePrinciple.unitsInclLinearMap L L' h x := by
  -- `unitsInclLinearMap` is the `Additive`-wrapped unit inclusion, so unwrap `Additive` first:
  -- it suffices to compare the two units of `L'`.
  rw [unitsInclLinearMap_apply]
  refine congrArg Additive.ofMul ?_
  -- The action of `Gal(K'/K)` on the units of a level is `Units.map` of the restriction, and
  -- `unitsInclHom` is `Units.map` of the field inclusion, so both sides are `Units.map`-images.
  change unitsInclHom L L' h ((levelRestrict L σ) • Additive.toMul x) =
    (levelRestrict L' σ) • unitsInclHom L L' h (Additive.toMul x)
  refine Units.ext ?_
  simp only [AlgEquiv.smul_units_def, unitsInclHom, Units.coe_map]
  -- It remains to compare the underlying elements in `K'`: both are `σ (↑x)`.
  refine Subtype.ext ?_
  change ((levelRestrict L σ) ((Additive.toMul x : (↥L)ˣ) : ↥L) : K') =
    ((levelRestrict L' σ)
      ((IntermediateField.inclusion h) ((Additive.toMul x : (↥L)ˣ) : ↥L)) : K')
  rw [AlgEquiv.restrictNormalHom_apply, AlgEquiv.restrictNormalHom_apply,
    IntermediateField.coe_inclusion]

end NK.HassePrinciple
