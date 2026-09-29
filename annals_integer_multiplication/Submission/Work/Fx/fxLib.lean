import Mathlib
import Submission.HvdH.Interfaces
import Submission.Work.Fx.FxCommon
import Submission.Work.Fx.FxExpAssemble
import Submission.Work.Fx.FxAdd
import Submission.Work.Fx.mulSField
import Submission.Work.Fx.mulFField
import Submission.Work.Fx.scaleField
import Submission.Work.Fx.cisField
import Submission.Work.Fx.expNegField
import Submission.Work.Fx.expPosField

set_option autoImplicit false

namespace Work.Fx

open HvdH

/-- Fixed-point complex arithmetic and exponential words (paper Lem. 2.1, 2.2, 2.4, 2.12-2.14). -/
theorem fxLib : HvdH.KernelLib → HvdH.IntLib → HvdH.FxLib := by
  intro hk hi
  obtain ⟨pA, KA, hA⟩ := addHalf_spec hk hi
  obtain ⟨pS, KS, hS⟩ := subHalf_spec hk hi
  obtain ⟨pM, KM, hM⟩ := mulSField hk hi
  obtain ⟨pF, KF, hF⟩ := mulFField hk hi
  obtain ⟨pSc, KSc, hSc⟩ := scaleField hk hi
  obtain ⟨pC, KC, hC⟩ := cisField hk hi (numWords hk hi)
  obtain ⟨pN, KN, hN⟩ := expNegField hk hi (numWords hk hi)
  obtain ⟨pP, KP, hP⟩ := expPosField hk hi (numWords hk hi)
  exact ⟨⟨pA, KA, hA⟩, ⟨pS, KS, hS⟩, ⟨pM, KM, hM⟩, ⟨pF, KF, hF⟩, ⟨pSc, KSc, hSc⟩,
    ⟨pC, KC, hC⟩, ⟨pN, KN, hN⟩, ⟨pP, KP, hP⟩⟩

end Work.Fx
