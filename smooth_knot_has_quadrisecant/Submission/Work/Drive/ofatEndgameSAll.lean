import Mathlib
import Submission.Work.Drive.ofatTopEndPin
import Submission.Work.Drive.crosscutOFatS
import Submission.Work.Drive.ofatEndgameSWiring

/-!
# The `OFat` endgame and the spread statement, from the top-end pin

`Work.Drive.ofatEndgameS_all` is `Work.Drive.OFatCrosscutEndgameS` for every smooth knot, from the
single pin `Work.Drive.ofatTopEndAll` (`Drive/ofatTopEndPin.lean`); combining it with the *proved*
`E3′` dichotomy `Work.Drive.ofatE3S_all` (`Drive/crosscutOFatS.lean`) gives the spread statement
`Work.Drive.SpreadQuadrisecantFullCloseK_v2` — the input of the limit passage
`Work.Drive.quadrisecant_of_genericCase_fullK_noHgen`.

This is the route of the deliverable
`Submission/Work/Drive/quadrisecant_of_genericCase_approx.lean`: the `S`-lane (`E3′` + the uniform-`ρ₀`
endgame) replaces the earlier `OFatCrosscutEndgame` pin, which the lead's
`NOTES_LEAD_endgameUniform.md` §0 shows cannot be discharged (the standard chamfer's separation
threshold is crosscut-dependent, and no uniform `δA` exists around an inflected reference knot).
-/

noncomputable section

namespace Work.Drive

open LeanEval.KnotTheory.Quadrisecant

/-- **The `OFat` endgame, from the top end.** -/
theorem ofatEndgameS_all : ∀ r : ℝ → Space, OFatCrosscutEndgameS r :=
  ofatEndgameS_of_topEnd ofatTopEndAll

/-- **The spread statement of the `S`-lane**: the `E3′` dichotomy (proved) + the endgame above. -/
theorem spreadQuadrisecantFullCloseK_of_OFatS : SpreadQuadrisecantFullCloseK_v2 :=
  spreadQuadrisecantFullCloseK_of_endgameS ofatE3S_all ofatEndgameS_all

end Work.Drive
