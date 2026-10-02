import Mathlib
import Submission.Work.Drive.Interfaces
import Submission.Work.Projective.CP4Concrete
import Submission.Work.Projective.Model
import Submission.Work.Projective.cp4_hc

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

/-!
# AREA GEN — `ℂP⁴` as a `Work.Drive.Smooth8`

The drive's generator `G₁` is `ℂP⁴` with its `C^∞` structure, its generating fundamental class
`Work.Projective.cp4C`, and the **defined** tangent-bundle classes `p₁Tangent'`, `p2Tangent'`.
This module provides the `Work.Drive.Smooth8` structure (the interface of
`Submission/Work/Drive/Interfaces.lean`), mirroring `Work.Thom.nonempty_closedOrientedSmooth8`
(which does the same for the `C¹` interface).
-/

open scoped Manifold ContDiff

namespace Work.Gen

open Work.Projective

noncomputable section

/-- The Euclidean charted-space structure on `ℂP⁴`, stated over the interface's model
`EuclideanSpace ℝ (Fin 8)` (definitionally the `Fin (2 * 4)` of `Work.Projective`). -/
abbrev cp4ChartedSpace : ChartedSpace (EuclideanSpace ℝ (Fin 8)) (CP 4) :=
  instChartedSpaceEuclidean 4

attribute [instance] cp4ChartedSpace

/-- The `C^∞` structure on `ℂP⁴`, stated over the interface's model. -/
abbrev cp4IsManifold : IsManifold (𝓡 8) ∞ (CP 4) :=
  Work.Projective.instIsManifoldEuclidean 4

attribute [instance] cp4IsManifold

/-- **`ℂP⁴` as a closed connected oriented `C^∞` `8`-manifold**, with the chosen generating
fundamental class `Work.Projective.cp4C`. -/
def cp4Smooth8 : Work.Drive.Smooth8 where
  pt := CP 4
  chartedSpace := cp4ChartedSpace
  isManifold := cp4IsManifold
  compactSpace := compactSpace_CP 4
  t2Space := t2Space_CP 4
  connectedSpace := connectedSpace_CP 4
  c := cp4C
  c_generates := cp4C_span

@[simp] theorem cp4Smooth8_pt : cp4Smooth8.pt = CP 4 := rfl

end

end Work.Gen
