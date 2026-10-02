import Mathlib
import Submission.Work.PTGeometric.RegionManifoldNCWeak
import Submission.Work.PTGeometric.RegionManifoldNC
import Submission.Work.PTGeometric.regionManifoldTheorem
import Submission.Work.PTGeometric.regionNhdBoundaryZero
import Submission.Work.PTGeometric.exists_chart_at_interior_zero
import Submission.Work.PTGeometric.WeakRegion.Setup
import Submission.Work.PTGeometric.WeakRegion.Manifold
import Submission.Work.PTGeometric.WeakRegion.Properties
import Submission.Work.PTGeometric.WeakRegion.PullChart

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# PTGEOMETRIC: the weak region-charting theorem

The region `{x | Φ x ≤ 0}` of the statement
`Work.PTGeometric.RegionManifoldTheoremOfIsCompactWeak` is a compact smooth manifold with boundary:
its charts are built in `Submission/Work/PTGeometric/WeakRegion/` (the per-point chart data in
`Setup.lean`, the charted space and smooth structure in `Manifold.lean`, and the transfer of
smoothness and submersivity in `Properties.lean` and `PullChart.lean`).  This file only assembles
the conclusion from those pieces: the manifold is the region itself and the homeomorphism is the
identity.
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

open scoped Manifold ContDiff Topology
open Function Set Topology Manifold Filter ModelWithCorners Classical

namespace Work.PTGeometric

noncomputable section

theorem regionManifoldTheorem_of_isCompact_weak (k : ℕ) :
    Work.PTGeometric.RegionManifoldTheoremOfIsCompactWeak k := by
  intro A _ _ _ _ Φ hΦ hweak hsign hone hK
  let S : Work.PTGeometric.WeakRegion.RegionSetupWeak k :=
    { A := A, Φ := Φ, hΦ := hΦ, hweak := hweak, hsign := hsign, hone := hone, hK := hK }
  letI : ChartedSpace (EuclideanHalfSpace (8 + k + 1)) S.Region := S.chartedSpaceOfRegion
  letI : IsManifold (𝓡∂ (8 + k + 1)) ∞ S.Region := S.isManifoldOfRegion
  letI : CompactSpace S.Region := S.compactSpaceOfRegion
  letI : T2Space S.Region := S.t2SpaceOfRegion
  refine ⟨S.Region, inferInstance, S.chartedSpaceOfRegion, S.isManifoldOfRegion,
    S.compactSpaceOfRegion, inferInstance, Homeomorph.refl S.Region, ?_, ?_, ?_, ?_⟩
  · intro m
    exact S.mem_boundary_iff m
  · intro F _ _ f hf
    exact hf.comp S.contMDiff_val
  · intro F _ _ f W hf
    exact S.contMDiffOn_comp_val F f W hf
  · intro F _ _ f m hm hf
    exact S.isSubmersionAt_comp_val f m hm hf

end

end Work.PTGeometric
