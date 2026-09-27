import Mathlib
import Submission.Work.Drive.famMeetDefs
import Submission.Work.Drive.sideCountDefs
import Submission.Work.Drive.sideValue
import Submission.Work.Drive.clampedSweep

/-!
# The design's count as a `famMeet`: the bridge from L6 to the locality `hn4`

`Work.Drive.coreSideCount Q c P` (`Submission/Work/Drive/sideCountDefs.lean`) counts the meets of the
core loop `t ↦ Q (exp (i π t))` of the chart with the clamped radial sweep of a plane presentation `P`.
The route `Work.Drive.parityCore_of_countOnZc_dense` (see
`Submission/Work/Drive/CHAINPARITY_REDUCTION.md`) needs its parity to be **locally constant in the
angle** (`hn4`), which is step L6 of the design, proved as `Work.Drive.odd_ncard_famMeet_iff`
(`Submission/Work/Drive/odd_ncard_famMeet_iff.lean`): the parity of `famMeet` at the two ends of a
regular family is the same.

This file defines the two maps that make the design's count an instance of `famMeet` — the loop side
`p ↦ coreLoop Q (p 1)` and the chain side `(t, x) ↦ clampedSweep c ψ (P t) x` for a *family* `t ↦ P t` of
plane presentations — and states the identification of the two meet sets (the only missing link).
-/

namespace Work.Drive

open Manifold
open scoped Manifold ContDiff

noncomputable section

/-- **The loop side of the design's count**, as a map on the two-box: `p ↦ coreLoop Q (p 1)`.  The
first coordinate `p 0` is the family parameter (carried along by `famMeet`), the second is the loop
parameter. -/
def coreLoopFam (Q : ℂ → CappingSpace) : EuclideanSpace ℝ (Fin 2) → CappingSpace :=
  fun p => coreLoop Q (p 1)

/-- **The chain side of the design's count**, as a map on the four-parameter chain space: the sweep of
the `t`-th member `P t` of a family of plane presentations, at the chain parameter `x = (q 1, q 2, q 3)`
and with the family parameter `t = q 0`. -/
def sweepFam (c : ℝ) (ψ : ℝ → ℝ) (P : ℝ → EuclideanSpace ℝ (Fin 2) → CappingSpace) :
    EuclideanSpace ℝ (Fin 4) → CappingSpace :=
  fun q => clampedSweep c ψ (P (q 0)) (famT3 (q 1) (q 2) (q 3))


/-- **The loop side of a *family of charts***: `p ↦ coreLoop (Q (p 0)) (p 1)`.  Used for the
perturbation-independence of the design's count, where the *chart* moves with `t` (the perturbation
`A t`) as well as the sweep. -/
def chartLoopFam (Q : ℝ → ℂ → CappingSpace) : EuclideanSpace ℝ (Fin 2) → CappingSpace :=
  fun p => coreLoop (Q (p 0)) (p 1)

/-- **The chain side of a *family of plane presentations***: `q ↦ clampedSweep c ψ (P (q 0)) (q 1,q 2,q 3)`.
The family parameter is the first coordinate, the chain parameter the last three. -/
def sweepFamP (c : ℝ) (ψ : ℝ → ℝ) (P : ℝ → EuclideanSpace ℝ (Fin 2) → CappingSpace) :
    EuclideanSpace ℝ (Fin 4) → CappingSpace :=
  fun q => clampedSweep c ψ (P (q 0)) (famT3 (q 1) (q 2) (q 3))

end

end Work.Drive
