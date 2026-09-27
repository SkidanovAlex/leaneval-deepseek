import Mathlib
import Submission.Work.Drive.disjoint_chartDisk_rotCapping_of_capSection
import Submission.Work.Drive.orbitXH
import Submission.Work.Drive.planeChain

/-!
# The whole-plane disjointness in the vocabulary of the consumers

`Work.Drive.disjoint_chartDisk_rotCapping_of_capSection` proves the disjointness of the chart's disk
from its own rotation, in the `chartDisk` vocabulary.  The consumers state it in the
`diskPlane`/`rotPresentation` vocabulary:

* `Work.Drive.avoidances_of_planeDisjoint` (`transportChartChains.lean`) takes
  `Disjoint (Set.range (diskPlane Q)) (Set.range P)` for `P` a swept plane — at the design's blocks
  `P = rotPresentation Q w`;
* `Work.Drive.sideGerm_spec`/`sideGerm_hn4` (`sideGerm.lean`) and `germHavoidZc` take
  `Disjoint (chartDisk Q) (rotCapping x '' chartDisk Q)` for `x ∈ Zc γ`.

This file converts, using the proved `range_diskPlane` and `range_rotPresentation_eq`, and adds the
two-rotation form `Disjoint (range (rotPresentation Q u)) (range (rotPresentation Q v))` for
`v - u ∈ Zc γ` — the shape of the transport's `hdisj₁`/`hdisj₂` at a block of the design's triple.
-/

namespace Work.Drive

open Manifold
open scoped Manifold ContDiff Topology

attribute [local instance] Work.Drive.cappingCharted Work.Drive.isManifold_cappingCharted
  Work.Drive.t2Space_cappingSpace Work.Drive.projCharted

noncomputable section


/-- The closed unit ball of `ℂ`, in the norm form used by the range lemmas. -/
private lemma closedBall_eq_norm_le : Metric.closedBall (0 : ℂ) 1 = {z : ℂ | ‖z‖ ≤ 1} := by
  ext z
  simp [Metric.mem_closedBall, dist_zero_right]

/-- **`Set.range (rotPresentation Q w)` is the rotation of the chart's disk.** -/
lemma range_rotPresentation (Q : ℂ → CappingSpace) (w : UnitAddCircle) :
    Set.range (rotPresentation Q w) = rotCapping w '' chartDisk Q := by
  have h1 : Set.range (rotPresentation Q w) = (rotCapping w ∘ Q) '' {z : ℂ | ‖z‖ ≤ 1} := by
    rw [rotPresentation, range_diskPlane]
    rfl
  rw [h1, chartDisk, Set.image_comp, closedBall_eq_norm_le]

/-- **The whole-plane disjointness of the chart's plane from its rotation**, in the
`diskPlane`/`rotPresentation` vocabulary, from `CapSection + CapInterior`. -/
theorem disjoint_range_diskPlane_rotPresentation_of_capSection {γ : Circle → ℝ × ℝ}
    (hγ : Manifold.IsSmoothEmbedding (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 1)))
      (modelWithCornersSelf ℝ (ℝ × ℝ)) ((⊤ : ℕ∞) : WithTop ℕ∞) γ)
    {hγne : ∀ x : Circle, γ x ≠ 0} {Q : ℂ → CappingSpace}
    (hQ : IsPlaneChart γ hγne Q)
    {μ : Circle × Circle → (ℝ × ℝ) × UnitAddCircle × ℝ}
    (hμne : ∀ x y : Circle, x ≠ y → μ (x, y) = Submission.Configuration.muOrd γ (x, y))
    (hμdiag : ∀ x : Circle, μ (x, x) = (γ x, tangentDirC γ x, 0))
    (hcap : CapSection Q) (hci : CapInterior Q)
    {w : UnitAddCircle} (hw : w ∈ Zc γ) :
    Disjoint (Set.range (diskPlane Q)) (Set.range (rotPresentation Q w)) := by
  have h := disjoint_chartDisk_rotCapping_of_capSection hγ hQ hμne hμdiag hcap hci hw
  rw [range_diskPlane, range_rotPresentation, closedBall_eq_norm_le.symm]
  exact h

/-- **The disjointness of two rotated presentations of one chart's plane** for `v - u ∈ Zc γ` — the
`hdisj₁`/`hdisj₂` shape of `Work.Drive.avoidances_of_planeDisjoint` at a block of the design's triple. -/
theorem disjoint_rotPresentation_rotPresentation_of_capSection {γ : Circle → ℝ × ℝ}
    (hγ : Manifold.IsSmoothEmbedding (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 1)))
      (modelWithCornersSelf ℝ (ℝ × ℝ)) ((⊤ : ℕ∞) : WithTop ℕ∞) γ)
    {hγne : ∀ x : Circle, γ x ≠ 0} {Q : ℂ → CappingSpace}
    (hQ : IsPlaneChart γ hγne Q)
    {μ : Circle × Circle → (ℝ × ℝ) × UnitAddCircle × ℝ}
    (hμne : ∀ x y : Circle, x ≠ y → μ (x, y) = Submission.Configuration.muOrd γ (x, y))
    (hμdiag : ∀ x : Circle, μ (x, x) = (γ x, tangentDirC γ x, 0))
    (hcap : CapSection Q) (hci : CapInterior Q)
    {u v : UnitAddCircle} (h : v - u ∈ Zc γ) :
    Disjoint (Set.range (rotPresentation Q u)) (Set.range (rotPresentation Q v)) := by
  have hbase := disjoint_range_diskPlane_rotPresentation_of_capSection hγ hQ hμne hμdiag hcap hci h
  rw [range_rotPresentation, range_diskPlane, closedBall_eq_norm_le.symm] at hbase
  rw [Set.disjoint_left] at hbase ⊢
  intro p hp hp'
  rw [range_rotPresentation] at hp
  rw [range_rotPresentation] at hp'
  obtain ⟨a, ha, rfl⟩ := hp
  obtain ⟨b, hb, hbp⟩ := hp'
  have h1 : a = rotCapping (v - u) b := by
    apply rotCapping_injective u
    rw [rotCapping_apply_add, ← hbp]
    congr 1
    abel
  exact hbase ha ⟨b, hb, h1.symm⟩

end

end Work.Drive
