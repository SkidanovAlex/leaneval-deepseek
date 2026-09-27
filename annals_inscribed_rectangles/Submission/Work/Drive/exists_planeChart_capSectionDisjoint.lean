import Mathlib
import Submission.Work.Drive.exists_planeChart_capSection_interior
import Submission.Work.Drive.disjoint_chartDisk_rotCapping_of_capSection
import Submission.Work.Drive.chartDiskDisjointInterface

/-!
# The consumer-ready whole-plane disjointness of a plane chart

The lead's target `Work.Drive.exists_planeChart_capSection_interior` produces a chart with
`IsPlaneChart`, `CapSection` and `CapInterior`; `Work.Drive.disjoint_chartDisk_rotCapping_of_capSection`
turns those three into the whole-plane disjointness.  This file packages the result in the
**unconditional, consumer-ready form**:

> `∃ Q, IsPlaneChart γ hγne Q ∧ ∀ w ∈ Zc γ, Disjoint (chartDisk Q) (rotCapping w '' chartDisk Q)`,

which is *verbatim* the hypothesis `hdisj` of `Work.Drive.sideGerm_spec`/`sideGerm_hn4`
(`sideGerm.lean`) and `germHavoidZc`, and — through
`Work.Drive.disjoint_rotPresentation_rotPresentation_of_capSection` and `Work.Drive.range_diskPlane` —
the `hdisj₁`/`hdisj₂` of the transport's `Work.Drive.avoidances_of_planeDisjoint`
(`transportChartChains.lean`).  The honest band data `μ` (`hμne`, `hμdiag`) are *definitional* for the
band of `γ`, so they are produced here rather than assumed.
-/

namespace Work.Drive

open Manifold
open scoped Manifold ContDiff Topology

attribute [local instance] Work.Drive.cappingCharted Work.Drive.isManifold_cappingCharted
  Work.Drive.t2Space_cappingSpace Work.Drive.projCharted

noncomputable section

/-- **The consumer-ready whole-plane disjointness of a plane chart** (H4 item (i), end to end): there is
a chart of the capped plane of `γ` whose disk is disjoint from each of its own rotations by a
collision-free angle. -/
theorem exists_planeChart_chartDisk_disjoint_capSection (hU : Submission.Drive.UmlaufProp)
    (γ : Circle → ℝ × ℝ)
    (hγ : Manifold.IsSmoothEmbedding (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 1)))
      (modelWithCornersSelf ℝ (ℝ × ℝ)) ((⊤ : ℕ∞) : WithTop ℕ∞) γ)
    (hγne : ∀ x : Circle, γ x ≠ 0) (hW : Work.Drive.WrapData γ) :
    ∃ Q : ℂ → CappingSpace,
      IsPlaneChart γ hγne Q ∧
      ∀ w : UnitAddCircle, w ∈ Zc γ →
        Disjoint (chartDisk Q) (rotCapping w '' chartDisk Q) := by
  classical
  obtain ⟨Q, hQ, hcap, hci⟩ := Work.Drive.exists_planeChart_capSection_interior hU γ hγ hγne hW
  refine ⟨Q, hQ, fun w hw => ?_⟩
  let μ : Circle × Circle → (ℝ × ℝ) × UnitAddCircle × ℝ :=
    fun q => if q.1 = q.2 then (γ q.1, Work.Drive.tangentDirC γ q.1, 0)
      else Submission.Configuration.muOrd γ q
  have hμne : ∀ x y : Circle, x ≠ y → μ (x, y) = Submission.Configuration.muOrd γ (x, y) := by
    intro x y hxy
    simp only [μ, if_neg hxy]
  have hμdiag : ∀ x : Circle, μ (x, x) = (γ x, Work.Drive.tangentDirC γ x, 0) := by
    intro x
    simp only [μ, if_pos rfl]
  exact Work.Drive.disjoint_chartDisk_rotCapping_of_capSection hγ hQ hμne hμdiag hcap hci hw

end

end Work.Drive
