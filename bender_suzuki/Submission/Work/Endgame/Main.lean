import Submission.Work.Endgame.Defs
import Submission.Work.Endgame.isStronglyEmbedded_map
import Submission.Work.Endgame.isStronglyEmbedded_comap
import Submission.Work.Endgame.hasFourGroup_iff_of_mulEquiv
import Submission.Work.Endgame.oddCore_eq_bot_of_isSimpleGroup_of_even
import Submission.Work.Endgame.oddCore_map_mulEquiv
import Submission.Work.Endgame.not_isStronglyEmbedded_of_not_hasFourGroup
import Submission.Work.Endgame.isSimpleBenderGroup_of_benderConclusion
import Submission.Work.Endgame.Type0

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# The endgame: `EndgameProp`

This module is the entry point of the area: it imports the whole chapter and proves its main
result.  `import Submission.Work.Endgame.Main` and use `Work.Endgame.endgame` is all a caller
needs; `Submission/Work/Endgame/NOTES.md` lists the contents and the conventions.

Theorem B (for groups in `Type`), Brauer–Suzuki and the model facts imply the challenge in every
universe `u`.  The only ingredient beyond the blueprint is the reduction of a finite group in
`Type u` to one in `Type 0`: transport the group structure of `X` to `Fin (Nat.card X)` along
`Nat.equivFinOfCardPos`, prove the statement there (`isSimpleBenderGroup_of_type0`, which lives in
universe `0`), and transport back along the resulting isomorphism
(`IsSimpleBenderGroup.of_mulEquiv`).

## The two local instances

`Fin n` already carries an unrelated `Mul` instance (`Fin.instMul`), and type class synthesis
prefers it over the `Mul` coming from a local `Group (Fin n)` instance when it constructs the
expected type of a `≃*` notation.  This is why the isomorphism `φ` below is introduced together
with an explicit local `Mul (Fin n)` instance (`transMul e.symm`); a local instance *does* shadow
`Fin.instMul`, after which all `≃*` notations mean the transported structure.
-/

set_option autoImplicit false
set_option linter.style.haveILetI false

open LeanEval.GroupTheory.Defs
open Submission.Blueprint

namespace Work.Endgame

theorem endgame.{u} (_hFT : FeitThompsonProp) : EndgameProp.{u} := by
  intro hB hBrSz hMod X hXgrp hXfin hXsimple M hM
  classical
  have hne : Nat.card X ≠ 0 := Nat.card_ne_zero.mpr ⟨⟨1⟩, inferInstance⟩
  let e : X ≃ Fin (Nat.card X) := Nat.equivFinOfCardPos hne
  letI : Group (Fin (Nat.card X)) := groupOfEquiv e.symm
  letI : Mul (Fin (Nat.card X)) := transMul e.symm
  let φ : Fin (Nat.card X) ≃* X := mulEquivOfEquiv e.symm
  haveI : IsSimpleGroup (Fin (Nat.card X)) := φ.isSimpleGroup
  have hstr : IsStronglyEmbedded (M.map φ.symm.toMonoidHom) := isStronglyEmbedded_map φ.symm hM
  have hres : IsSimpleBenderGroup (Fin (Nat.card X)) :=
    isSimpleBenderGroup_of_type0 hB hBrSz hMod (Fin (Nat.card X)) (M.map φ.symm.toMonoidHom) hstr
  exact IsSimpleBenderGroup.of_mulEquiv hres φ

/-- The endgame, applied: `EndgameProp` unfolded at a concrete group and strongly embedded
subgroup.  This is the form the blueprint's assembly uses. -/
theorem endgame_apply.{u} (hFT : FeitThompsonProp) (hB : TheoremB) (hBrSz : BrauerSuzukiProp)
    (hMod : ModelFactsProp) {X : Type u} [Group X] [Finite X] [IsSimpleGroup X] (M : Subgroup X)
    (hM : IsStronglyEmbedded M) : IsSimpleBenderGroup X :=
  endgame hFT hB hBrSz hMod X M hM

end Work.Endgame
