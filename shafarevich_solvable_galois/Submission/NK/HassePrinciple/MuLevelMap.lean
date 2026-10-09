/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The transition morphism of the `μ_p` level system

Umbrella development: `Submission/Work/HassePrinciple/` (README §8.4 item 1, §10.4).

The `μ_p` analogue of `NK.HassePrinciple.unitsLevelMap`: the transition morphism

`muLevelMap p V h : MuLevelH2 p V L ⟶ MuLevelH2 p V L'`

of the `μ_p` level system in this chapter's vocabulary (`MuLevel.lean`,
`exists_muLevelMapCoeff.lean`), for a level inclusion `h : L ≤ L'`.
-/

import Submission.NK.HassePrinciple.MuLevel
import Submission.NK.HassePrinciple.exists_muLevelMapCoeff
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

/-- **The transition morphism of the `μ_p` level system**: inflation along
`LevelGroup V L' →* LevelGroup V L` together with the coefficient inclusion `μ_p(L) → μ_p(L')`. -/
noncomputable def muLevelMap (p : ℕ) (V : Subgroup Gal(K'/K))
    {L L' : FiniteGaloisIntermediateField K K'} (h : L ≤ L') :
    MuLevelH2 p V L ⟶ MuLevelH2 p V L' :=
  groupCohomology.map (levelQuotHom (U := V) h) (muLevelMapCoeff p V h) 2

/-- The computation rule for the `μ_p` transition morphism. -/
theorem muLevelMap_apply (p : ℕ) (V : Subgroup Gal(K'/K))
    {L L' : FiniteGaloisIntermediateField K K'} (h : L ≤ L') (x : MuLevelH2 p V L) :
    (muLevelMap p V h).hom x =
      (groupCohomology.map (levelQuotHom (U := V) h) (muLevelMapCoeff p V h) 2).hom x := rfl

end NK.HassePrinciple
