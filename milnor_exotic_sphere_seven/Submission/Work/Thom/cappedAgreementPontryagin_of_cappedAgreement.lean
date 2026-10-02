import Mathlib
import Submission.Work.Thom.cappedAgreement
import Submission.Work.TangentClasses.Capped

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

namespace Work.Thom

/-- `CappedAgreement` (agreement of `p1Tangent'` with the tangent-bundle class
`Work.TangentClasses.p1Tangent F hF S`, up to sign) implies `CappedAgreement'` (agreement of
`p1Tangent'` with `Work.Milnor.cappedPontryaginClass`, up to sign): combine the hypothesis with the
unconditional `Work.TangentClasses.p1Tangent_eq_pm_cappedPontryaginClass`, which says that
`p1Tangent F hF S` itself is `± cappedPontryaginClass F hF`.  Note that the two signs may be
different, but `CappedAgreement'` only asks that `p1Tangent'` be one of the two classes
`± cappedPontryaginClass`, so the composite of the two signs is irrelevant. -/
theorem cappedAgreementPontryagin_of_cappedAgreement
    {F : Submission.Milnor.Mk (-2) → Work.Milnor.Sph8}
    {hF : Work.Milnor.IsCappingDiffeo F} (S : Work.TangentClasses.DiscTangentSplitting)
    (h : Work.Thom.CappedAgreement F hF S) : Work.Thom.CappedAgreement' F hF := by
  rcases h with h | h <;>
    rcases Work.TangentClasses.p1Tangent_eq_pm_cappedPontryaginClass F hF S with hp | hp
  · exact Or.inl (h.trans hp)
  · exact Or.inr (h.trans hp)
  · exact Or.inr (by rw [h, hp])
  · exact Or.inl (by rw [h, hp]; simp)

end Work.Thom
