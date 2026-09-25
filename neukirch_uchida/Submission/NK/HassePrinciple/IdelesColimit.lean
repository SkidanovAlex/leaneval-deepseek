/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The idèle level objects, towards the colimit idèle group `𝕀_{LE}`

Umbrella development: `Submission/Work/HassePrinciple/` (the limit passage, README §13.5).

The limit Hasse–Brauer–Noether theorem needs the idèle group of the *infinite* extension
`E = K'^U` (there is no such object in the workspace, and no `NumberField` instance for `E`), so —
exactly as for the units in `UnitsLevel.lean`/`UnitsColimit.lean` — it is realised *at the level of
the levels*: the coefficient module at the level `L` is `𝕀_L = Idele ↥L`, made a representation of
the finite level group `LevelGroup V L` by restricting along
`levelGroupRestrictHom V L : LevelGroup V L →* Gal(↥L/K)`, and the cohomology of the level is
`H²(LevelGroup V L, 𝕀_L)`.

This module provides the level objects only:

* `NK.HassePrinciple.ideleLevelRep` — `𝕀_L` as a `CoeffInt`-linear representation of the level
  group `LevelGroup V L`, together with its computation rule `ideleLevelRep_ρ_apply`;
* `NK.HassePrinciple.IdeleLevelH2` — the level cohomology `H²(LevelGroup V L, 𝕀_L)`.

The next brick (to be built on top of this file) is the *transition system*: the equivariant maps
`𝕀_L → 𝕀_{L'}` attached to a level inclusion `L ≤ L'`, their coherence, the resulting
`NK.BrauerTwist.LevelSystem` and its colimit — the idèle counterpart of
`NK.HassePrinciple.H2Units` — together with the grade-two map to the idèle class group
(`classGroupRep`, `classGroupMap`) and the localisation maps of the Shapiro argument.
-/

import Submission.NK.HassePrinciple.UnitsLevel
import Submission.NK.HassePrinciple.IdelesLevel

open CategoryTheory Representation
open NK.GlobalCFT
open scoped NumberField

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 400000
set_option linter.unusedSectionVars false

universe u

namespace NK.HassePrinciple

open NK.BrauerHasse

variable {K K' : Type u} [Field K] [NumberField K] [Field K'] [Algebra K K'] [IsSepClosure K K']

/-! ## The level group acting on the idèles -/

/-- **The representation of the level group `LevelGroup V L` on the idèles `𝕀_L`**: the idèle
representation `ideleRep K ↥L` of `Gal(↥L/K)` restricted along
`levelGroupRestrictHom V L : LevelGroup V L →* Gal(↥L/K)`.  This is the idèle counterpart of
`unitsLevelRep`. -/
noncomputable abbrev ideleLevelRep (V : Subgroup Gal(K'/K))
    (L : FiniteGaloisIntermediateField K K') : Rep CoeffInt (LevelGroup V L) :=
  Rep.res (levelGroupRestrictHom V L) (ideleRep K ↥L)

/-- The action of the level group on `𝕀_L`, computed at the class of an element of `V`. -/
theorem ideleLevelRep_ρ_apply (V : Subgroup Gal(K'/K))
    (L : FiniteGaloisIntermediateField K K') (v : ↥V)
    (x : Additive (Idele ↥L)) :
    (ideleLevelRep V L).ρ (QuotientGroup.mk v) x = (levelRestrict L (v : Gal(K'/K))) • x := rfl

/-- **The idèle level cohomology** `H²(V ⧸ (V ⊓ Gal(K'/L)), 𝕀_L)`, the idèle counterpart of
`UnitsLevelH2`. -/
noncomputable abbrev IdeleLevelH2 (V : Subgroup Gal(K'/K))
    (L : FiniteGaloisIntermediateField K K') : ModuleCat CoeffInt :=
  groupCohomology (ideleLevelRep V L) 2

/-- **The class-group level representation**: `C_L` as a representation of the level group, the
counterpart of `ideleLevelRep` for the idèle class group. -/
noncomputable abbrev classGroupLevelRep (V : Subgroup Gal(K'/K))
    (L : FiniteGaloisIntermediateField K K') : Rep CoeffInt (LevelGroup V L) :=
  Rep.res (levelGroupRestrictHom V L) (classGroupRep K ↥L)

/-- **The idèle class group level cohomology** `H²(V ⧸ (V ⊓ Gal(K'/L)), C_L)`. -/
noncomputable abbrev ClassGroupLevelH2 (V : Subgroup Gal(K'/K))
    (L : FiniteGaloisIntermediateField K K') : ModuleCat CoeffInt :=
  groupCohomology (classGroupLevelRep V L) 2

/-! ## The transition map: specification

The transition of the idèle level system `L ↦ IdeleLevelH2 V L` along a level inclusion `L ≤ L'` is
built from the push-forward of idèles `𝕀_L → 𝕀_{L'}`: choose for each place `w` of `L'` the place
`u w` of `L` below it (`Place.LiesOver`, unique by
`Submission/Work/GlobalCFT/Inclusion/globalCFT_liesOver_unique.lean`) and push the `(u w)`-component
forward along the local unit embedding `Place.localAlgebraMapUnits`.  The specification is pinned as a
`Prop` so that it can be handed to a prover as a single goal; the equivariance of the resulting map
with the Galois action is the existing result
`NK.GlobalCFT.Inclusion.globalCFT_ideleInclusion_smul`. -/

/-- **Specification of the push-forward of idèles along a finite extension `L/K`**: a monoid
homomorphism `𝕀_K →* 𝕀_L` whose `w`-component is the `(u w)`-component of the input, transported
along the local unit embedding at `w`. -/
def IdelePushSpec (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] : Prop :=
  ∃ (φ : 𝕀[K] →* 𝕀[L]) (u : Place L → Place K) (hu : ∀ w : Place L, Place.LiesOver w (u w)),
    ∀ (x : 𝕀[K]) (w : Place L),
      φ x w = Place.localAlgebraMapUnits w (u w) (hu w) (x (u w))

end NK.HassePrinciple
