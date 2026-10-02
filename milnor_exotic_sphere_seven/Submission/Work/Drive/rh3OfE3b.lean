import Submission.Work.Serre.serreE3a
import Submission.Work.Serre.serreC3FiniteOne
import Submission.Work.Stems.c2FreeMain
import Submission.Work.Stems.rangeModelRatAcyclic3
import Submission.Work.RatHurewicz.S3Final

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000
/-- **Rational Hurewicz (stable-3 form) from SerreE3b alone.** Every other input is proved: SerreE3a,
SerreC3FiniteOne, the C2 odd free-top induction (c = 3), and the range-model reduction. Checked by the lead,
2026-09-26: axioms = propext, Classical.choice, Quot.sound. -/
theorem Work.Drive.rh3_of_e3b (h : Work.Serre.SerreE3b) : Work.Drive.RationalHurewiczStable3 :=
  Work.RatHurewicz.rationalHurewiczStable3_of_rangeModel
    (Work.Stems.rangeModelRatAcyclic_of_C2odd_C3one 3
      (Work.Stems.c2oddFree_three Work.Serre.serreE3a h) Work.Serre.serreC3FiniteOne)
