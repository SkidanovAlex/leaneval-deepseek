/-
# `Submission.Work.FIPiChain.Unconditional` --- the challenge, with area 4 taken from disk

`Work.FIArea4.area4_6c` is the proved area 4 (`Work.FITop4.Area4_6c`); areas 1, 2, 3, 6, τ, 7 are
consumed from disk inside `Work.FIFinal.prop41`.  Hence, with this chapter's `challenge_of_area4`,
the Friedlander–Iwaniec theorem follows with **no remaining input**.  (This module is separated from
`P5.lean` so that the delivery interface `Work.FIPiChain.challenge_of_area4` does not drag in the
whole area-4 dependency cone.)

Both `Work.FIArea4.area4_6c` and `Work.FIPiChain.friedlander_iwaniec_unconditional` are axiom-clean
(`propext`, `Classical.choice`, `Quot.sound`).  To close the workspace's own top-level statement,
`Submission.lean`'s `theorem friedlander_iwaniec := by sorry` becomes

    import Submission.Work.FIPiChain.Unconditional
    ...
    theorem friedlander_iwaniec : {p : ℕ | p.Prime ∧ ∃ a b, p = a ^ 2 + b ^ 4}.Infinite :=
      Work.FIPiChain.friedlander_iwaniec_unconditional

(that file is the final assembly point and is left to the lead).
-/
import Mathlib
import Submission.Work.FIPiChain.P5
import Submission.Work.FIArea4.area4_6c

set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace Work.FIPiChain

/-- **The Friedlander–Iwaniec theorem**, from the delivered interface and the on-disk area 4. -/
theorem friedlander_iwaniec_unconditional :
    {p : ℕ | p.Prime ∧ ∃ a b : ℕ, p = a ^ 2 + b ^ 4}.Infinite :=
  challenge_of_area4 Work.FIArea4.area4_6c

#print axioms Work.FIPiChain.friedlander_iwaniec_unconditional

end Work.FIPiChain
