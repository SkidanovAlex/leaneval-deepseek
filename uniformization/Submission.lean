import ChallengeDeps
import Submission.Work.Drive.Interfaces
import Submission.Work.Drive.periodsHold_of_subsingleton_hom
import Submission.Work.Drive.weak_case
import Submission.Work.Drive.liouville_case

/-! The closure imports `Mathlib.Analysis.CStarAlgebra.Classes` (via `import Mathlib` and the Poisson
kernel), whose `instCommCStarAlgebraComplex` would otherwise be found first for `NormedCommRing ℂ`
and change how `Solution.lean` elaborates the fixed statement (the comparator then reports a
statement mismatch). Demoting that parent projection restores the elaboration of `ChallengeDeps`
exactly (checked by diffing the `pp.all` statement). -/
attribute [instance 1] CommCStarAlgebra.toNormedCommRing

open LeanEval.Geometry
open scoped Manifold ContDiff

namespace Submission

theorem uniformization {X : Type*} [TopologicalSpace X] [T2Space X] [ConnectedSpace X]
    [SecondCountableTopology X] [ChartedSpace ℂ X] [IsManifold mℂ 1 X]
    (hX : ¬ CompactSpace X) (x : X) [Subsingleton <| Additive (FundamentalGroup X x) →+ ℝ] :
    Nonempty (X ≃ₘ⟮mℂ, mℂ⟯ ℂ) ∨ Nonempty (X ≃ₘ⟮mℂ, mℂ⟯ UpperHalfPlane) :=
  Work.Drive.uniformization_of_parts hX x
    (Work.Drive.periodsHold_of_subsingleton_hom hX x)
    (fun hP hW => Work.Drive.weak_case hX x hP hW)
    (fun hP hO => Work.Drive.liouville_case hX x hP hO)

end Submission
