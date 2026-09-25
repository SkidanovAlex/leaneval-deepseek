import Submission.GroupTheory.GolodShafarevichCriterion
import Submission.Commons.GroupTheory.ProPGroup.golod_shafarevich_presentation_card_lt

/-!
# Chapter B is DONE: the finite `p`-group Golod--Shafarevich inequality

`Submission.GroupTheory.FinitePGroupGolodShafarevich p` -- "every nontrivial finite
`p`-group with a minimal generating set of size `d` and any presentation with `r`
relators satisfies `4r > d^2`" -- is exactly the conclusion of the commons lemma
`Commons.GroupTheory.ProPGroup.golod_shafarevich_presentation_card_lt`, which is
proved, sorry-free, 3098 lines, with the SAME hypotheses.

This file is the one-line bridge between them. Historical note for whoever reads
this: the previous run spent ~50 hours of agent time delegating a chain
(L481 -> L489 -> L502) that was re-proving this from scratch, because the parent
never learned that the commons already had it. Do not start a Magnus/Jennings
chapter: it is not needed for the Martinet endgame.
-/

namespace Submission.GroupTheory

open Commons.GroupTheory.ProPGroup

/-- **Chapter B, discharged.** The finite `p`-group Golod--Shafarevich inequality,
from the proved commons lemma. -/
theorem finitePGroupGolodShafarevich_of_commons (p : ℕ) [Fact p.Prime] :
    FinitePGroupGolodShafarevich p := by
  intro α _ _ Q _ _ _ rel hQ hpres hgen
  exact golod_shafarevich_presentation_card_lt p hQ rel hpres hgen

end Submission.GroupTheory
