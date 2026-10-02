import Mathlib
import Submission.Work.Agree.S4Bundle
import Submission.Work.Milnor.VBundle
import Submission.Work.TangentClasses.Tangent
import Submission.Work.Thom.manifoldP1
import Submission.Work.TangentClasses.DiscSplitting
import Submission.Work.Thom.complexPullback

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

open scoped Manifold ContDiff Topology
open TopologicalSpace Set

/-!
# The two-chart cover of the disc bundle `Vk (-2)`, and the splitting of its tangent bundle

`Submission.Milnor.Vk k = (vData k).Glued` is the total space of the rank-`4` real bundle `ξ_k` over
`S⁴`, obtained by glueing two copies of `MSpace8 = ℝ⁴ × ℍ` along `{x ≠ 0} × ℍ`: so its atlas (the
glueing atlas `Submission.Glue.Data.instChartedSpace`) is the range of `chartAt`, whose values are
the two charts of the two copies.  The cover used below picks the charts at the two distinguished
points `ιX 0` and `ιY 0`; their sources are the images of the two pieces, whose union is everything.

The tangent bundle of `Vk (-2)` is the two-chart bundle over those two pieces whose transition is the
derivative of the glueing map `vMap (-2)`; the point of this file is to make that presentation
*finite* (so that `Work.Thom.chernClass` applies) and to state the splitting of the tangent bundle
as the pullback of `TS⁴ ⊕ ξ`.
-/

namespace Work.Agree

open Work.TangentClasses

noncomputable section

open Classical

/-- The disc bundle of Milnor's `ξ`. -/
abbrev Vk : Type := Submission.Milnor.Vk (-2)

/-- **The two-chart cover of `Vk (-2)`**: the charts of the glueing at the two distinguished points
`ιX 0` and `ιY 0`. -/
def vkCover : Fin 2 → atlas Submission.Milnor.MSpace8 Vk := fun i =>
  if i = 0 then ⟨(Submission.Milnor.vData (-2)).chartAt ((Submission.Milnor.vData (-2)).ιX 0),
      ChartedSpace.chart_mem_atlas ((Submission.Milnor.vData (-2)).ιX 0)⟩
  else ⟨(Submission.Milnor.vData (-2)).chartAt ((Submission.Milnor.vData (-2)).ιY 0),
      ChartedSpace.chart_mem_atlas ((Submission.Milnor.vData (-2)).ιY 0)⟩

@[simp] lemma vkCover_zero :
    vkCover 0 = ⟨(Submission.Milnor.vData (-2)).chartAt ((Submission.Milnor.vData (-2)).ιX 0),
      ChartedSpace.chart_mem_atlas ((Submission.Milnor.vData (-2)).ιX 0)⟩ := rfl

@[simp] lemma vkCover_one :
    vkCover 1 = ⟨(Submission.Milnor.vData (-2)).chartAt ((Submission.Milnor.vData (-2)).ιY 0),
      ChartedSpace.chart_mem_atlas ((Submission.Milnor.vData (-2)).ιY 0)⟩ := rfl

/-- **The two-chart presentation of the tangent bundle of the disc bundle**, over the finite cover
`Work.Agree.vkCover`. -/
def vkTangent (h : ∀ x : Vk, ∃ i, x ∈ (Work.TangentClasses.tangentBundle
    Work.Milnor.mMSpace8 Vk).baseSet (vkCover i)) :
    RealBundle Vk Submission.Milnor.MSpace8 (Fin 2) :=
  (Work.TangentClasses.tangentBundle Work.Milnor.mMSpace8 Vk).reindex vkCover h


end

end Work.Agree
