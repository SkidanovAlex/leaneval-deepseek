import Mathlib
import Submission.Work.Milnor.NoCapping
import Submission.Work.Drive.Interfaces
import Submission.Work.Drive.hirz8_of_generators_thom
import Submission.Work.Gen.generators8
import Submission.Work.Agree.agreeAll
import Submission.Work.Stems.stableStemsTorsion
import Submission.Work.ThomBordism.thomRational

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# Final wiring (project lead)

`CappedCongruence`, the dimension-8 Hirzebruch congruence for the capped family, from the four
proved areas: `Gen.generators8`, `ThomBordism.thomRational` (fed `Stems.stableStemsTorsion`),
`Drive.hirz8_of_generators_thom` and `Agree.agreeAll`, through `Drive.cappedCongruence_of_areas`.
This replaces the placeholder `Work.Milnor.cappedCongruence` (the `sorry` in
`CongruenceInterface.lean`) on the path of the main theorem.
-/

namespace Work.Milnor

theorem cappedCongruence_proved : CappedCongruence :=
  Work.Drive.cappedCongruence_of_areas
    (Work.Drive.hirz8_of_generators_thom Work.Gen.generators8
      (Work.ThomBordism.thomRational Work.Stems.stableStemsTorsion))
    Work.Agree.agreeAll

theorem no_cappingDiffeo_proved (F : Submission.Milnor.Mk (-2) →
    (Metric.sphere (0 : EuclideanSpace ℝ (Fin 8)) 1)) (hF : IsCappingDiffeo F) : False :=
  no_cappingDiffeo_of_cappedCongruence cappedCongruence_proved F hF

end Work.Milnor
