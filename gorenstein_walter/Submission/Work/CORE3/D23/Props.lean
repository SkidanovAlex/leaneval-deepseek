import Mathlib
import Submission.Work.CORE3.D23.Core23A
import Submission.Work.CORE3.D23.InvolActionUniform
import Submission.Work.CORE3.D23.FittingFaithfulFour
import Submission.Work.CORE3.D23.CardUOfFittingThree

/-!
# CORE3 / D23: the three leaves of Bender's step (7) as the `Core23A` Props

`Work.CORE3.D23.J4U3V18s` takes the three leaves of design pass 23 §A as the hypotheses
`hL1 : InvolActionUniformProp`, `hL3 : FittingFaithfulFourProp` and
`hL4 : CardUOfFittingThreeProp`.  The modules
`Submission/Work/CORE3/D23/{InvolActionUniform,FittingFaithfulFour,CardUOfFittingThree}.lean`
prove the unfolded forms; this module repacks them as those Props.
-/

namespace Work.CORE3.D23

/-- The unfolded form `Work.CORE3.D23.FittingFaithfulFour`, as the design's Prop. -/
theorem fittingFaithfulFourProp : FittingFaithfulFourProp :=
  fun G _ _ I h B h1 D g Y hYF hYH hV => FittingFaithfulFour G I h B h1 D g Y hYF hYH hV

/-- The unfolded form `Work.CORE3.D23.CardUOfFittingThree`, as the design's Prop. -/
theorem cardUOfFittingThreeProp : CardUOfFittingThreeProp :=
  fun G _ _ I h B h1 D hF => CardUOfFittingThree G I h B h1 D hF

end Work.CORE3.D23
