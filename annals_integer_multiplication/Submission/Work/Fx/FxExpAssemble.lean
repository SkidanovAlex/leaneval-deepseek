import Submission.Work.Fx.FxExpCore
import Submission.Work.Fx.piWord
import Submission.Work.Fx.logTwoWord
import Submission.Work.Fx.expCplx

/-!
# Assembling `NumWords` from the primitive numerical words
-/

set_option autoImplicit false

namespace Work.Fx

open HvdH

theorem numWords (hk : KernelLib) (hi : IntLib) : NumWords hk hi :=
  ⟨piWord hk hi, logTwoWord hk hi, expCplx hk hi⟩

end Work.Fx
