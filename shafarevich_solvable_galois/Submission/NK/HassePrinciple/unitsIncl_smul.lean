import Mathlib.FieldTheory.IsSepClosed
import Mathlib.FieldTheory.Galois.GaloisClosure
import Submission.NK.HassePrinciple.UnitsLevel
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

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
