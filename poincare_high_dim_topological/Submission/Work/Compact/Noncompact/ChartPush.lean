import Mathlib
import Submission.Work.Geo.Euclid.EuclidPush

/-!
# The chart conjugate of the Euclidean radial push

For a chart `e : OpenPartialHomeomorph M E` of a topological space, a base point `p : E` and a
threshold `L : ℝ`, `chartPush e p L s` is the self-map of `M` which on the chart source is the
conjugate of the Euclidean radial push `Work.Geo.Radial.pushGen p L s` and which is the identity
outside the chart source:

`chartPush e p L s z = e.symm (pushGen p L s (e z))` for `z ∈ e.source`, and `z` otherwise.

It is the self-map of `M` whose restriction to the complement of `{y}`, for `p = e y`, is the
homotopy inverse of the inclusion `Kᶜ ↪ {y}ᶜ` of
`Submission/Work/Compact/Noncompact/exists_homotopyEquiv_compl_closedBall.lean`.
-/

open Set Metric
open scoped Topology unitInterval

namespace Work.Compact.Noncompact

noncomputable section

variable {M : Type*} [TopologicalSpace M]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The chart conjugate of the parametrised radial push `Work.Geo.Radial.pushGen`: on the chart
source it pushes radially away from `p`, outside the chart source it is the identity. -/
def chartPush (e : OpenPartialHomeomorph M E) (p : E) (L : ℝ) (s : ℝ) (z : M) : M := by
  classical
  exact if z ∈ e.source then e.symm (Work.Geo.Radial.pushGen p L s (e z)) else z

lemma chartPush_of_mem {e : OpenPartialHomeomorph M E} {p : E} {L s : ℝ} {z : M}
    (hz : z ∈ e.source) :
    chartPush e p L s z = e.symm (Work.Geo.Radial.pushGen p L s (e z)) := by
  rw [chartPush, if_pos hz]

lemma chartPush_of_notMem {e : OpenPartialHomeomorph M E} {p : E} {L s : ℝ} {z : M}
    (hz : z ∉ e.source) : chartPush e p L s z = z := by
  rw [chartPush, if_neg hz]

/-- At time `1` the chart push is the identity. -/
lemma chartPush_one {e : OpenPartialHomeomorph M E} (p : E) (L : ℝ) (z : M) :
    chartPush e p L 1 z = z := by
  rw [chartPush]
  by_cases hz : z ∈ e.source
  · rw [if_pos hz, Work.Geo.Radial.pushGen_one, e.left_inv hz]
  · rw [if_neg hz]

/-- **The chart push preserves the complement of a chart preimage.**  If `z` is in the chart
source and the push of `e z` (at time `s`) is a point of the chart target which lies outside `C`,
then `chartPush e p L s z` lies outside `e.source ∩ e ⁻¹' C`. -/
lemma chartPush_notMem_compl {e : OpenPartialHomeomorph M E} {p : E} {L : ℝ} {C : Set E}
    {s : ℝ} {z : M} (hz : z ∈ e.source)
    (hmap : Work.Geo.Radial.pushGen p L s (e z) ∈ e.target)
    (hzC : Work.Geo.Radial.pushGen p L s (e z) ∉ C) :
    chartPush e p L s z ∉ e.source ∩ e ⁻¹' C := by
  rw [chartPush_of_mem hz]
  intro hmem
  have h2 : e (e.symm (Work.Geo.Radial.pushGen p L s (e z))) ∈ C := hmem.2
  rw [e.right_inv hmap] at h2
  exact hzC h2

/-- The chart push does not hit `y` when the push of `e z` does not hit `p = e y`. -/
lemma chartPush_ne {e : OpenPartialHomeomorph M E} {p : E} {L : ℝ} {s : ℝ} {z y : M}
    (hz : z ∈ e.source) (hmap : Work.Geo.Radial.pushGen p L s (e z) ∈ e.target)
    (hzp : Work.Geo.Radial.pushGen p L s (e z) ≠ p) (hey : e y = p) :
    chartPush e p L s z ≠ y := by
  rw [chartPush_of_mem hz]
  intro hcon
  have h2 : Work.Geo.Radial.pushGen p L s (e z) = e y := by
    rw [← e.right_inv hmap, hcon]
  exact hzp (by rw [h2, hey])

end

end Work.Compact.Noncompact
