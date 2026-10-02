import Mathlib
import Submission.Work.Thom.cappedAgreement
import Submission.Work.Thom.cappedCongruenceTangent_of_hirzebruchCongruence8
import Submission.Work.Milnor.CongruenceInterface

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

namespace Work.Thom

theorem no_cappingDiffeo_of_hirzebruchCongruence8 (h : Work.Thom.HirzebruchCongruence8)
    (hagree : ∀ (F : Submission.Milnor.Mk (-2) → Work.Milnor.Sph8)
      (hF : Work.Milnor.IsCappingDiffeo F), Work.Thom.CappedAgreement' F hF) :
    ∀ (F : Submission.Milnor.Mk (-2) → Work.Milnor.Sph8) (hF : Work.Milnor.IsCappingDiffeo F),
      False :=
  Work.Milnor.no_cappingDiffeo_of_cappedCongruence
    (Work.Thom.cappedCongruence_of_cappedCongruenceTangent
      (Work.Thom.cappedCongruenceTangent_of_hirzebruchCongruence8 h) hagree)

end Work.Thom
