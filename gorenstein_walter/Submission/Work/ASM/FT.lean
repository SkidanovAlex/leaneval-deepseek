import Submission.OddOrder.FeitThompson
import Submission.Work.ASM.Defs

/-!
# ASM: Feit–Thompson in the vocabulary of this development

The whole `gorenstein_walter` build consumes Feit–Thompson through the `Prop`
`Work.GW2.FeitThompsonProp` (`Submission.Work.ASM.Defs`).  This file discharges it from the
ported odd-order library (`Submission.OddOrder.FeitThompson`, third-party, do not edit), so that
a caller never has to mention the library directly.
-/

namespace Work.GW2

/-- Feit–Thompson in the vocabulary of `Work.GW2`: every finite group of odd order is solvable. -/
theorem feitThompsonProp : FeitThompsonProp := fun _ _ _ h => OddOrder.feitThompson h

end Work.GW2
