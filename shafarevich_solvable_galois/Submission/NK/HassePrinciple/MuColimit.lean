/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The colimit of the `μ_p` level system, and the Kummer map on colimits

Umbrella development: `Submission/Work/HassePrinciple/` (README §8.4 item 1, §10.4).

The `μ_p` counterpart of `Submission/Work/HassePrinciple/UnitsColimit.lean`: the
`NK.BrauerTwist.LevelSystem` of the level data `L ↦ H²(LevelGroup V L, μ_p(L))`
(`MuLevel.lean`, `MuLevelMap.lean`, `muLevelMap_refl.lean`, `muLevelMap_comp.lean`) and its
colimit `MuColim p V`, together with the **Kummer map on the colimits**

`kummerColim p V : MuColim p V → H2Units V`

induced by the level-wise `NK.HassePrinciple.kummerLevel` and its naturality
(`NK.HassePrinciple.kummerLevel_naturality`) through the universal property of the colimit.

What remains of item 1 of §8.4 after this is the injectivity of `kummerColim` (README §10.4).
-/

import Submission.NK.BrauerTwist.System
import Submission.NK.HassePrinciple.MuLevelMap
import Submission.NK.HassePrinciple.muLevelMap_refl
import Submission.NK.HassePrinciple.muLevelMap_comp
import Submission.NK.HassePrinciple.UnitsColimit
import Submission.NK.HassePrinciple.KummerLevel
import Submission.NK.HassePrinciple.kummerLevel_naturality
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

open CategoryTheory

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option linter.unusedSectionVars false

universe u

namespace NK.HassePrinciple

open NK.BrauerHasse

variable {K K' : Type u} [Field K] [Field K'] [Algebra K K'] [IsSepClosure K K']

/-- **The `μ_p` level system in this chapter's vocabulary**: the level data
`L ↦ H²(LevelGroup V L, μ_p(L))` with the transition maps `muLevelMap` and their coherence laws. -/
noncomputable def muLevelSystem (p : ℕ) (V : Subgroup Gal(K'/K)) :
    NK.BrauerTwist.LevelSystem K K' where
  obj L := MuLevelH2 p V L
  map := fun {_ _} (h : _ ≤ _) =>
    muLevelMap p V ((FiniteGaloisIntermediateField.le_iff _ _).mp h)
  map_refl := fun L x => by
    have h : muLevelMap p V ((FiniteGaloisIntermediateField.le_iff L L).mp (le_refl L)) =
        muLevelMap p V (le_refl (L : IntermediateField K K')) :=
      congrArg (fun hh => muLevelMap p V hh) (Subsingleton.elim _ _)
    rw [h]
    exact congrArg (fun f => f.hom x) (muLevelMap_refl p V L)
  map_comp := fun h₁ h₂ x => by
    have := congrArg (fun f => f.hom x) (muLevelMap_comp p V
      ((FiniteGaloisIntermediateField.le_iff _ _).mp h₁)
      ((FiniteGaloisIntermediateField.le_iff _ _).mp h₂))
    rw [ModuleCat.hom_comp, LinearMap.comp_apply] at this
    rw [this]

/-- **The `μ_p` colimit** `colim_L H²(LevelGroup V L, μ_p(L))`, the counterpart of the units
colimit `NK.HassePrinciple.H2Units`. -/
noncomputable abbrev MuColim (p : ℕ) (V : Subgroup Gal(K'/K)) : Type u := (muLevelSystem p V).Colim

/-- The structure map from a level into the `μ_p` colimit. -/
noncomputable abbrev MuColim.ofLevel (p : ℕ) (V : Subgroup Gal(K'/K))
    (L : FiniteGaloisIntermediateField K K') (a : MuLevelH2 p V L) : MuColim p V :=
  (muLevelSystem p V).ofLevel L a

/-- **The Kummer map on the colimits**: the level-wise Kummer morphisms assemble, through the
universal property of the colimit, into a map `colim_L H²(LevelGroup V L, μ_p(L)) ⟶
colim_L H²(LevelGroup V L, Lˣ)`.  Item 1 of README §8.4 is the injectivity of this map. -/
noncomputable def kummerColim (p : ℕ) (V : Subgroup Gal(K'/K)) : MuColim p V → H2Units V :=
  (muLevelSystem p V).lift (fun L a => H2Units.ofLevel V L ((kummerLevel p V L) a)) (by
    intro L L' h a
    have hn : (unitsLevelMap V ((FiniteGaloisIntermediateField.le_iff L L').mp h))
        ((kummerLevel p V L) a) =
        (kummerLevel p V L')
          ((muLevelMap p V ((FiniteGaloisIntermediateField.le_iff L L').mp h)) a) := by
      have hh := congrArg (fun f => f.hom a)
        (kummerLevel_naturality p V ((FiniteGaloisIntermediateField.le_iff L L').mp h))
      change (unitsLevelMap V ((FiniteGaloisIntermediateField.le_iff L L').mp h)).hom
          ((kummerLevel p V L).hom a) =
        (kummerLevel p V L').hom
          ((muLevelMap p V ((FiniteGaloisIntermediateField.le_iff L L').mp h)).hom a) at hh
      exact hh
    show H2Units.ofLevel V L'
      ((kummerLevel p V L')
        ((muLevelMap p V ((FiniteGaloisIntermediateField.le_iff L L').mp h)) a)) =
      H2Units.ofLevel V L ((kummerLevel p V L) a)
    rw [← hn]
    exact (unitsLevelSystem V).ofLevel_map h ((kummerLevel p V L) a))

/-- The computation rule for the Kummer map on the colimits. -/
@[simp]
theorem kummerColim_ofLevel (p : ℕ) (V : Subgroup Gal(K'/K))
    (L : FiniteGaloisIntermediateField K K') (a : MuLevelH2 p V L) :
    kummerColim p V (MuColim.ofLevel p V L a) = H2Units.ofLevel V L ((kummerLevel p V L) a) :=
  rfl

end NK.HassePrinciple
