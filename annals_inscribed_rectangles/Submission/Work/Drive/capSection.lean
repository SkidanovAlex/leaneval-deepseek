import Mathlib
import Submission.Work.Drive.cappedPlaneDisjoint
import Submission.Work.Drive.sideGermDefs

/-!
# `CapSection`: the chart's inner disk does not meet its own rotations

The transport's T6 (`Work.Drive.odd_topBdryMeet_zero_iff_coreSideCounts`) needs the **whole-plane**
disjointness `Disjoint (Set.range (diskPlane P_u)) (Set.range P_v)` for `v - u ∈ Zc γ`, i.e. the
*disjointness of the capped planes*.  In the chart's own coordinates this splits into three pieces:

* strip against strip — `Work.Drive.disjoint_stripImage_rot` (proved);
* strip interior against cap — `Work.Drive.mk_inl_ne_mk_inr_of_norm_lt_one`, i.e. the interiors of the
  two pieces of `CappingSpace` are disjoint (`cappingRel` glues boundary points only);
* **cap against cap** — the content of this file: the inner disk `‖z‖ ≤ 1/2` of the chart must not meet
  its own image under a rotation `rotCapping w` with `w ≠ 0`.

The hypothesis that makes the third piece *readable* is

> **`CapSection Q`**: `‖z‖ ≤ 1/2 → ‖z'‖ ≤ 1/2 → Q z = rotCapping w (Q z') → w = 0`.

It is exactly the statement that the *caps* `cap_0` and `cap_w` of the chart are disjoint for `w ≠ 0`
(in the chart's own parametrisation), and it is the piece that the existing `IsPlaneChart`'s clauses do
*not* provide: clause 4 only says that the inner disk maps into *some* cap point.  The cap must be
chosen (a capping) so that the property holds; see the note at the end of this file.
-/

namespace Work.Drive

open Manifold
open scoped Manifold ContDiff Topology

attribute [local instance] Work.Drive.cappingCharted Work.Drive.isManifold_cappingCharted
  Work.Drive.t2Space_cappingSpace Work.Drive.projCharted

noncomputable section

/-- **The cap section property of a chart**: points of the closed inner half-disk (`‖z‖ ≤ 1/2`) of the
chart that differ by a rotation of the configuration must be equal — equivalently, the cap of the chart
meets its own rotations only for the trivial rotation `w = 0`. -/
def CapSection (Q : ℂ → CappingSpace) : Prop :=
  ∀ (z z' : ℂ) (w : UnitAddCircle), ‖z‖ ≤ 1 / 2 → ‖z'‖ ≤ 1 / 2 → Q z = rotCapping w (Q z') → w = 0

/-- **`CapSection` excludes rotations in `Zc γ`.**  Since `0 ∉ Zc γ` (`Work.Drive.zero_notMem_Zc`),
two inner-disk points of a chart with `CapSection` can never differ by a rotation `w ∈ Zc γ`. -/
theorem eq_zero_of_capSection_of_mem_Zc {Q : ℂ → CappingSpace} (h : CapSection Q)
    {γ : Circle → ℝ × ℝ} {w : UnitAddCircle} (hw : w ∈ Zc γ) {z z' : ℂ}
    (hz : ‖z‖ ≤ 1 / 2) (hz' : ‖z'‖ ≤ 1 / 2) (heq : Q z = rotCapping w (Q z')) : False :=
  ne_zero_of_mem_Zc hw (h z z' w hz hz' heq)

/-- **The cap of the chart does not meet its own rotated cap** (for `w ∈ Zc γ`), in the chart's
coordinates.  This is the "cap against cap" piece of the whole-plane disjointness
`Disjoint (range (diskPlane Q)) (Set.range (rotPresentation Q w))`. -/
theorem disjoint_chartInner_rot_of_Zc {Q : ℂ → CappingSpace} (h : CapSection Q)
    {γ : Circle → ℝ × ℝ} {w : UnitAddCircle} (hw : w ∈ Zc γ) :
    Disjoint (Q '' Metric.closedBall (0 : ℂ) (1 / 2))
      (rotCapping w '' (Q '' Metric.closedBall (0 : ℂ) (1 / 2))) := by
  rw [Set.disjoint_left]
  rintro p ⟨z, hz, rfl⟩ ⟨s, hs, hsp⟩
  obtain ⟨z', hz', rfl⟩ := hs
  exact eq_zero_of_capSection_of_mem_Zc h hw
    (by simpa [Metric.mem_closedBall, dist_zero_right] using hz)
    (by simpa [Metric.mem_closedBall, dist_zero_right] using hz') hsp.symm

end

end Work.Drive
