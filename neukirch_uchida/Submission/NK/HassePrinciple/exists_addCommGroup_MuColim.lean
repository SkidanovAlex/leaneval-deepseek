/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Addition in the `μ_p` colimit `MuColim p V`: the `AddCommGroup` instance

Umbrella development: `Submission/Work/HassePrinciple/` (README §8.4 item 1, §10.4).

`NK.HassePrinciple.MuColim p V` is the filtered colimit of the level cohomologies
`L ↦ MuLevelH2 p V L = H²(LevelGroup V L, μ_p(L))` along the transition maps `muLevelMap`.  Every
level is a `CoeffInt`-module and the transition maps are `CoeffInt`-linear, so the additive
structure descends to the colimit: two classes represented at levels `L`, `L'` are added by
inflating both to the join `L ⊔ L'` (which dominates both, the finite Galois intermediate fields
being directed under `⊔`) and adding there.

* `Submission/Work/HassePrinciple/MuColimAdd.lean` defines the operations `muJoinAdd` (addition),
  `muColimZero` (the class of `0` at the bottom level `⊥`) and `muColimNeg` (negation), together
  with their evaluation rules `muJoinAdd_ofLevel`, `muJoinAdd_ofLevel_le` (the sum evaluated at any
  common upper bound of the two levels) and `muJoinAdd_ofLevel_self` (the level-wise addition);
* the group axioms of `muJoinAdd` are proved in the separate modules
  `muJoinAdd_comm`, `muJoinAdd_assoc`, `muJoinAdd_zero_left`, `muJoinAdd_zero_right`,
  `muColimNeg_add_cancel`.

This file assembles them into the requested `AddCommGroup (MuColim p V)` instance, whose addition,
zero and negation are `muJoinAdd`, `muColimZero` and `muColimNeg`, and for which `MuColim.ofLevel`
is additive (the last component of the statement below, from `muJoinAdd_ofLevel_self`).

The content of the individual axioms is the usual one for a filtered colimit: `ofLevel` is
surjective, so everything reduces to level representatives; the level lattices
(`sup_assoc`, `sup_comm`, `bot_le`) move the representatives to a common level, and there the
transition maps' additivity (`muLevelSystem_map_add`) and their coherence laws reduce the claim to
the corresponding axiom in the level module `MuLevelH2 p V M` (`add_assoc`, `add_comm`, `zero_add`,
`add_zero`, `neg_add_cancel`).
-/

import Mathlib
import Submission.NK.HassePrinciple.MuColimAdd
import Submission.NK.HassePrinciple.muJoinAdd_comm
import Submission.NK.HassePrinciple.muJoinAdd_assoc
import Submission.NK.HassePrinciple.muJoinAdd_zero_left
import Submission.NK.HassePrinciple.muJoinAdd_zero_right
import Submission.NK.HassePrinciple.muColimNeg_add_cancel

set_option linter.style.haveILetI false

universe u

namespace NK.HassePrinciple

/-- **The `μ_p` colimit `MuColim p V` is an additive commutative group**, with addition
`muJoinAdd`, zero `muColimZero` and negation `muColimNeg`, and with the structure maps
`MuColim.ofLevel` additive: `ofLevel L (a + b) = ofLevel L a + ofLevel L b` for all classes `a`,
`b` of a level `L`.

The instance is built from the three operations of `MuColimAdd.lean` (declared as local `Add`,
`Zero` and `Neg` instances so that the structure fields can be written with the standard notation)
and the five group axioms of `muJoinAdd` proved in the modules imported above. -/
theorem exists_addCommGroup_MuColim {K K' : Type u} [Field K] [Field K'] [Algebra K K'] [IsSepClosure K K']
    (p : ℕ) (V : Subgroup (K' ≃ₐ[K] K')) :
    ∃ (inst : AddCommGroup (NK.HassePrinciple.MuColim p V)),
      letI := inst
      ∀ (L : FiniteGaloisIntermediateField K K') (a b : NK.HassePrinciple.MuLevelH2 p V L),
        NK.HassePrinciple.MuColim.ofLevel p V L (a + b) =
          NK.HassePrinciple.MuColim.ofLevel p V L a + NK.HassePrinciple.MuColim.ofLevel p V L b := by
  letI : Add (MuColim p V) := ⟨muJoinAdd p V⟩
  letI : Zero (MuColim p V) := ⟨muColimZero p V⟩
  letI : Neg (MuColim p V) := ⟨muColimNeg p V⟩
  let inst : AddCommGroup (MuColim p V) :=
    { add_assoc := muJoinAdd_assoc p V
      zero_add := muJoinAdd_zero_left p V
      add_zero := muJoinAdd_zero_right p V
      neg_add_cancel := muColimNeg_add_cancel p V
      add_comm := muJoinAdd_comm p V
      nsmul := nsmulRec
      zsmul := zsmulRec }
  exact ⟨inst, fun L a b => (muJoinAdd_ofLevel_self p V L a b).symm⟩

end NK.HassePrinciple
