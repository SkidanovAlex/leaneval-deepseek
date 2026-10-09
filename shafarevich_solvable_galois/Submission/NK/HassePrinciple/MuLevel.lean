/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The `μ_p` level system in this chapter's vocabulary

Umbrella development: `Submission/Work/HassePrinciple/` (README §8.4 item 1, §10.4).

The sibling area `Submission/Work/BrauerTwist/` builds the level cohomology
`H²(Gal(K'/K) ⧸ Gal(K'/L), μ_p(L))` — representations of the *quotient group*
`Gal(K'/K) ⧸ Gal(K'/L)`.  The units level system of this chapter
(`Submission/Work/HassePrinciple/UnitsLevel.lean`) carries its representations over `Gal(L/K)`
(instead of the quotient), so the Kummer map `H²(·, μ_p) → H²(·, Lˣ)` cannot be stated level-wise by
mixing the two vocabularies, even though the groups are isomorphic.  This file builds the `μ_p` side
in this chapter's own vocabulary, mirroring `UnitsLevel.lean`:

* `NK.HassePrinciple.muLevelRep p V L` — the representation of `LevelGroup V L` on `μ_p(L)`;
* `NK.HassePrinciple.MuLevelH2 p V L = H²(LevelGroup V L, μ_p(L))`;
* `NK.HassePrinciple.muLevelIncl`, `NK.HassePrinciple.muLevelInclLinearMap` — the coefficient
  inclusion `μ_p(L) → μ_p(L')` for a level inclusion.

The equivariance of `muLevelInclLinearMap` (as in `NK.HassePrinciple.unitsIncl_smul`), the
transition morphism, and the Kummer morphism `MuLevelH2 → UnitsLevelH2` are the remaining steps
(README §10.4).
-/

import Submission.NK.HassePrinciple.UnitsLevel
import Submission.NK.HassePrinciple.Mu
import Mathlib.RingTheory.RootsOfUnity.Basic
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

open CategoryTheory Representation

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 400000
set_option linter.unusedSectionVars false

universe u

namespace NK.HassePrinciple

open NK.BrauerHasse

variable {K K' : Type u} [Field K] [Field K'] [Algebra K K'] [IsSepClosure K K']

/-- **The representation of the level group on `μ_p(L)`**, in this chapter's vocabulary: the
pullback of `NK.HassePrinciple.muRep` along the restriction `LevelGroup V L →* Gal(L/K)`. -/
noncomputable abbrev muLevelRep (p : ℕ) (V : Subgroup Gal(K'/K))
    (L : FiniteGaloisIntermediateField K K') : Rep CoeffInt (LevelGroup V L) :=
  Rep.res (levelGroupRestrictHom V L) (muRep p K ↥L)

/-- **The `μ_p` level cohomology** `H²(U ⧸ (U ⊓ Gal(K'/L)), μ_p(L))`. -/
noncomputable abbrev MuLevelH2 (p : ℕ) (V : Subgroup Gal(K'/K))
    (L : FiniteGaloisIntermediateField K K') : ModuleCat CoeffInt :=
  groupCohomology (muLevelRep p V L) 2

/-- The inclusion `μ_p(L) → μ_p(L')` of roots of unity attached to a level inclusion, as a monoid
homomorphism. -/
noncomputable def muLevelIncl (p : ℕ) (L L' : FiniteGaloisIntermediateField K K') (h : L ≤ L') :
    ↥(rootsOfUnity p ↥L) →* ↥(rootsOfUnity p ↥L') where
  toFun x := ⟨Units.map (IntermediateField.inclusion h).toMonoidHom (x : (↥L)ˣ),
    (mem_rootsOfUnity p _).mpr (by
      rw [← map_pow, (mem_rootsOfUnity p (x : (↥L)ˣ)).mp x.2, map_one])⟩
  map_one' := by ext; simp
  map_mul' x y := by ext; simp [map_mul]

/-- The coefficient inclusion as a `CoeffInt`-linear map on the additive groups. -/
noncomputable def muLevelInclLinearMap (p : ℕ) (L L' : FiniteGaloisIntermediateField K K')
    (h : L ≤ L') :
    Additive ↥(rootsOfUnity p ↥L) →ₗ[CoeffInt] Additive ↥(rootsOfUnity p ↥L') where
  toFun x := Additive.ofMul (muLevelIncl p L L' h (Additive.toMul x))
  map_add' x y := by
    change Additive.ofMul (muLevelIncl p L L' h (Additive.toMul x * Additive.toMul y)) =
      Additive.ofMul (muLevelIncl p L L' h (Additive.toMul x)) +
        Additive.ofMul (muLevelIncl p L L' h (Additive.toMul y))
    rw [map_mul]
    rfl
  map_smul' n x := by
    obtain ⟨z⟩ := n
    show Additive.ofMul (muLevelIncl p L L' h ((Additive.toMul x) ^ z)) =
      Additive.ofMul ((muLevelIncl p L L' h (Additive.toMul x)) ^ z)
    rw [map_zpow]

/-- The computation rule for `muLevelInclLinearMap`. -/
theorem muLevelInclLinearMap_apply (p : ℕ) (L L' : FiniteGaloisIntermediateField K K')
    (h : L ≤ L') (x : Additive ↥(rootsOfUnity p ↥L)) :
    muLevelInclLinearMap p L L' h x =
      Additive.ofMul (muLevelIncl p L L' h (Additive.toMul x)) := rfl

end NK.HassePrinciple
