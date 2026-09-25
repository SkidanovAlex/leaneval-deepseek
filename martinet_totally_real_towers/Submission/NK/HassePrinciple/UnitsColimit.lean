/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The colimit of the units level system: `H2Units`

Umbrella development: `Submission/Work/HassePrinciple/` (README §8.4 item 1, §10.4).

`Submission/Work/HassePrinciple/UnitsLevel.lean` and `.../exists_unitsLevelMapCoeff.lean` build the
level cohomology `H²(LevelGroup V L, Lˣ)` and its transition morphisms, and
`.../unitsLevelMap_refl.lean`, `.../unitsLevelMap_comp.lean` are their coherence laws.  This file
packages them as a `NK.BrauerTwist.LevelSystem` — the coefficient-generic filtered-colimit
machinery of the sibling area — and takes its colimit:

`NK.HassePrinciple.H2Units V = colim_L H²(LevelGroup V L, Lˣ)`,

the units counterpart of the `μ_p` colimit `NK.BrauerTwist.H2Twist` (which is the classical
continuous `H²(V, μ_p)`).  The colimit comes with the structure maps `ofLevel` and the universal
property `lift`/`lift_ofLevel`/`lift_unique` of `NK.BrauerTwist.LevelSystem`, and with the equality
criterion `ofLevel_eq_iff`.

The remaining steps of README §8.4 item 1 are the Kummer morphism
`H2Twist V → H2Units V` (level-wise `groupCohomology.map (MonoidHom.id _) (kummerIncl ...) 2`, with
naturality in the level) and its injectivity; see README §10.4.
-/

import Submission.NK.BrauerTwist.System
import Submission.NK.HassePrinciple.unitsLevelMap_refl
import Submission.NK.HassePrinciple.unitsLevelMap_comp

open CategoryTheory

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option linter.unusedSectionVars false

universe u

namespace NK.HassePrinciple

open NK.BrauerHasse

variable {K K' : Type u} [Field K] [Field K'] [Algebra K K'] [IsSepClosure K K']

/-- **The units level system**: the system of level data `L ↦ H²(LevelGroup V L, Lˣ)` with the
transition maps `unitsLevelMap` and their coherence laws. -/
noncomputable def unitsLevelSystem (V : Subgroup Gal(K'/K)) : NK.BrauerTwist.LevelSystem K K' where
  obj L := UnitsLevelH2 V L
  map := fun {_ _} (h : _ ≤ _) =>
    unitsLevelMap V ((FiniteGaloisIntermediateField.le_iff _ _).mp h)
  map_refl := fun L x => by
    have h : unitsLevelMap V ((FiniteGaloisIntermediateField.le_iff L L).mp (le_refl L)) =
        unitsLevelMap V (le_refl (L : IntermediateField K K')) :=
      congrArg (fun hh => unitsLevelMap V hh) (Subsingleton.elim _ _)
    rw [h]
    exact congrArg (fun f => f.hom x) (unitsLevelMap_refl V L)
  map_comp := fun h₁ h₂ x => by
    have := congrArg (fun f => f.hom x) (unitsLevelMap_comp V
      ((FiniteGaloisIntermediateField.le_iff _ _).mp h₁)
      ((FiniteGaloisIntermediateField.le_iff _ _).mp h₂))
    rw [ModuleCat.hom_comp, LinearMap.comp_apply] at this
    rw [this]

/-- **The units colimit** `colim_L H²(LevelGroup V L, Lˣ)`, the units counterpart of
`NK.BrauerTwist.H2Twist`. -/
noncomputable abbrev H2Units (V : Subgroup Gal(K'/K)) : Type u := (unitsLevelSystem V).Colim

/-- The structure map from a level into the units colimit. -/
noncomputable abbrev H2Units.ofLevel (V : Subgroup Gal(K'/K))
    (L : FiniteGaloisIntermediateField K K') (a : UnitsLevelH2 V L) : H2Units V :=
  (unitsLevelSystem V).ofLevel L a

end NK.HassePrinciple
