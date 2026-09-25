/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Equivariance of the `μ_p` coefficient inclusion

Umbrella development: `Submission/Work/HassePrinciple/` (README §8.4 item 1, §10.4).

The `μ_p`-analogue of `NK.HassePrinciple.unitsIncl_smul` for the `μ_p` level system built in
`Submission/Work/HassePrinciple/MuLevel.lean`: the coefficient inclusion `μ_p(L) → μ_p(L')` is
equivariant for the two restriction actions.
-/

import Submission.NK.HassePrinciple.MuLevel

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 400000
set_option linter.unusedSectionVars false

universe u

namespace NK.HassePrinciple

open NK.BrauerHasse

/-- **Equivariance of the `μ_p` coefficient inclusion.**  For `σ ∈ Gal(K'/K)` the inclusion
`μ_p(L) → μ_p(L')` intertwines the action of the restriction of `σ` to `L` with the action of the
restriction of `σ` to `L'`. -/
theorem muLevelIncl_smul {K K' : Type u} [Field K] [Field K'] [Algebra K K'] [IsSepClosure K K']
    (p : ℕ) (L L' : FiniteGaloisIntermediateField K K') (h : L ≤ L') (σ : K' ≃ₐ[K] K')
    (x : Additive ↥(rootsOfUnity p ↥L)) :
    muLevelInclLinearMap p L L' h ((levelRestrict L σ) • x) =
      (levelRestrict L' σ) • muLevelInclLinearMap p L L' h x := by
  rw [muLevelInclLinearMap_apply]
  refine congrArg Additive.ofMul ?_
  change muLevelIncl p L L' h ((levelRestrict L σ) • Additive.toMul x) =
    (levelRestrict L' σ) • muLevelIncl p L L' h (Additive.toMul x)
  refine Subtype.ext ?_
  rw [show ((muLevelIncl p L L' h ((levelRestrict L σ) • Additive.toMul x)
      : ↥(rootsOfUnity p ↥L')) : (↥L')ˣ)
      = Units.map (IntermediateField.inclusion h).toMonoidHom
          ((((levelRestrict L σ) • Additive.toMul x : ↥(rootsOfUnity p ↥L)) : (↥L)ˣ)) from rfl]
  rw [coe_smul_rootsOfUnity, coe_smul_rootsOfUnity]
  refine Units.ext ?_
  simp only [AlgEquiv.smul_units_def, Units.coe_map]
  refine Subtype.ext ?_
  change ((levelRestrict L σ)
      ((Additive.toMul x : ↥(rootsOfUnity p ↥L)) : (↥L)ˣ) : K') =
    ((levelRestrict L' σ) (Units.map (IntermediateField.inclusion h).toMonoidHom
      ((Additive.toMul x : ↥(rootsOfUnity p ↥L)) : (↥L)ˣ)) : K')
  rw [AlgEquiv.restrictNormalHom_apply, AlgEquiv.restrictNormalHom_apply]
  rfl

end NK.HassePrinciple
