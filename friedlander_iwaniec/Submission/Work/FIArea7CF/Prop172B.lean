/-
# `Submission.Work.FIArea7CF.Prop172B` — `Prop172Classical` from the proved (21.9)

The composition of `Submission/Work/FIArea7/prop172Unconditional.lean`, but with `Prop213` supplied
by `Submission.Work.FIArea7CF.Prop213FinalB`, i.e. by the *proved* `Pub213.holder6_bound`
(*FI* (21.9)) rather than by the interface `Pub213.Hyp3`.  See NOTES §63.
-/
import Mathlib
import Submission.Work.FIArea7CF.Prop213FinalB
import Submission.Work.FIArea7.prop214
import Submission.Work.FIArea7.prop231
import Submission.Work.FIArea7.theorem2psi
import Submission.Work.FIArea7.prop172classical
import Submission.Work.FIArea7.prop232Done

set_option autoImplicit false

namespace Work.FIArea7

/-- ***FI* Proposition 17.2, unconditional** (the composition of `prop172Unconditional`, with the
*proved* (21.9) in place of its interface). -/
theorem prop172UnconditionalB : Work.FIArea7.Prop172Classical :=
  let h31 : Work.FIArea7.Prop231 := prop231 (prop214 Work.FIArea7.Pub213.prop213Pub)
  prop172classical h31 prop232Done (theorem2psi h31 prop232Done)

end Work.FIArea7
