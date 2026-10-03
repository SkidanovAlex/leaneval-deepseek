import Mathlib
import Submission.Work.Peluse.UControl.petChapter5_of_levelChainV3_aux
import Submission.Work.Peluse.UControl.petDirAbsLe

/-!
# `PetChapter5` from the level chain (the `V3` assembly)

The final wrapper: the assembly `petChapter5_of_levelChainV3_aux` takes the two inputs that are
*about the terminal state of the phase-1 chain* as hypotheses, and they are supplied here by

* `terminalShiftBoundL` — the `ShiftBound` of `histTerminal P hd` at range `c` with constant
  `Cs · c^P.natDegree · ⌈A⌉₊` (the range is needed by the level chain, whose `Nstep + 1 ≤ c`),
* `petDir_abs_leH` — the uniform bound on the datum's direction (`Cs · H^(l-1)`, `Cs` independent
  of `H`).

So the single remaining obligation for `PetChapter5` is `PetLevelChain P` (the level chain itself):
`petChapter5Holds P := petChapter5_of_levelChainV3 P (petLevelChain P)`.
-/

set_option autoImplicit false
open scoped BigOperators

namespace Work.Peluse.UControl

noncomputable section

theorem petChapter5_of_levelChainV3 (P : Polynomial ℤ) (h : PetLevelChain P) :
    PetChapter5 P :=
  petChapter5_of_levelChainV3_aux P h
    (fun hd => terminalShiftBoundL P hd)
    (fun E l hl c => petDir_abs_leH E l hl c)

end

end Work.Peluse.UControl
