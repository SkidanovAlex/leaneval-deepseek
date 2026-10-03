import Submission.Lib.Unif2.Work.Drive.Interfaces
import Submission.Lib.Unif2.Work.Drive.periodsHold_of_subsingleton_hom
import Submission.Lib.Unif2.Work.Drive.weak_case
import Submission.Lib.Unif2.Work.Drive.liouville_case
import Submission.Work.Interfaces.Fatou

/-!
# Discharging `MandelDim.UniformizationHyp` (lead)

The uniformization theorem of our uniformization library (copied, sorry-free closure under
`Submission/Lib/Unif2`, ChallengeDeps replaced by the shim `Submission.Lib.Unif2.UnifDeps`),
restated as `MandelDim.UniformizationHyp`. Same proof as that library's root `Submission.lean`.
-/

open LeanEval.Geometry
open scoped Manifold ContDiff

namespace MandelDim

theorem uniformizationHyp : UniformizationHyp := by
  intro X _ _ _ _ _ _ hX x hsub
  haveI := hsub
  exact Work.Drive.uniformization_of_parts hX x
    (Work.Drive.periodsHold_of_subsingleton_hom hX x)
    (fun hP hW => Work.Drive.weak_case hX x hP hW)
    (fun hP hO => Work.Drive.liouville_case hX x hP hO)

end MandelDim
