import Mathlib
import Submission.Work.Milnor.VBundleDefs
import Submission.Work.Milnor.vMap_smooth
import Submission.Work.Milnor.vMap_inv
import Submission.Work.Glue.Basic
import Submission.Work.Glue.glued_isManifold
import Submission.Work.Glue.mem_groupoid_of_contMDiffOn

/-!
# The open disc bundle over `S⁴` as a smooth 8-manifold

Assembly of `Submission.Work.Milnor.VBundleDefs`: the two-chart clutching description of the total
space of the rank-4 vector bundle `ξ` over `S⁴` is a gluing of two copies of `ℝ⁴ × ℍ` in the sense
of `Submission.Glue.Data`, hence carries a `ChartedSpace` and an `IsManifold` structure.

The smoothness of the clutching map and its inverse laws are the delegated lemmas
`Work.Milnor.vMap_smooth` and `Work.Milnor.vMap_inv`.
-/

namespace Submission.Milnor

open scoped Manifold ContDiff Topology
open TopologicalSpace Set

noncomputable section

/-- The clutching map, as an open partial homeomorphism of `ℝ⁴ × ℍ`. -/
def vPartialHomeomorph (k : ℤ) : OpenPartialHomeomorph MSpace8 MSpace8 where
  toFun := vMap k
  invFun := vMapInv k
  source := vOpens
  target := vOpens
  map_source' := fun _ hp => invBase_ne_zero hp
  map_target' := fun _ hp => invBase_ne_zero hp
  left_inv' := fun p hp => (Work.Milnor.vMap_inv k hp).1
  right_inv' := fun p hp => (Work.Milnor.vMap_inv k hp).2
  continuousOn_toFun := (Work.Milnor.vMap_smooth k).1.continuousOn
  continuousOn_invFun := (Work.Milnor.vMap_smooth k).2.continuousOn
  open_source := vOpens.2
  open_target := vOpens.2

/-- The gluing data whose `Glued` space is the total space of the vector bundle `ξ`. -/
noncomputable def vData (k : ℤ) : Submission.Glue.Data 𝓘(ℝ, MSpace8) ∞ MSpace8 MSpace8 where
  U := vOpens
  V := vOpens
  isOpen_U := vOpens.2
  isOpen_V := vOpens.2
  φ := vPartialHomeomorph k
  source_φ := rfl
  target_φ := rfl
  mem_groupoid :=
    Work.Glue.mem_groupoid_of_contMDiffOn (Work.Milnor.vMap_smooth k).1
      (Work.Milnor.vMap_smooth k).2

/-- **The total space of the rank-4 vector bundle `ξ` over `S⁴`** (equivalently the open disc
bundle): the quotient of two copies of `ℝ⁴ × ℍ` glued along `{x ≠ 0} × ℍ` by the clutching map. -/
abbrev Vk (k : ℤ) : Type := (vData k).Glued

instance instTopologicalSpaceVk (k : ℤ) : TopologicalSpace (Vk k) :=
  Submission.Glue.Data.instTopologicalSpace (vData k)

instance instChartedSpaceVk (k : ℤ) : ChartedSpace MSpace8 (Vk k) :=
  Submission.Glue.Data.instChartedSpace (vData k)

instance instIsManifoldVk (k : ℤ) : IsManifold 𝓘(ℝ, MSpace8) ∞ (Vk k) :=
  Work.Glue.glued_isManifold (vData k)

end

end Submission.Milnor
