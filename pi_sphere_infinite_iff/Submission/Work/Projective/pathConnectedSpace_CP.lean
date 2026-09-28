import Mathlib
import Submission.Work.Projective.CPn

/-!
# `ℂPⁿ` is path connected

Complex projective space `ℂPⁿ = Work.Projective.CP n` is covered by its affine charts
`chartSet i`, each of which is the continuous image of `Fin n → ℂ` under `chartInv i`; and every
chart contains the point `allOnesCP n = [1 : ⋯ : 1]`.  Hence any two points of `ℂPⁿ` can be joined
by a path through `[1 : ⋯ : 1]`:

* if `p ∈ chartSet i`, then `t ↦ chartInv i ((1 - t) • chartFun i p + t • chartFun i [1:⋯:1])`
  is a path from `p` to `[1 : ⋯ : 1]` which lies entirely in the chart `i` (the interpolation is
  pulled back through the continuous parametrisation `chartInv i`, so no non-degeneracy is
  needed — this is the path-connected counterpart of `Work.Projective.connectedSpace_CP`, which
  uses the same point `[1 : ⋯ : 1]` to glue the charts).

The main result is `Work.Projective.pathConnectedSpace_CP`.
-/

open scoped Manifold ContDiff Topology

namespace Work.Projective

noncomputable section

/-- **Every point of `ℂPⁿ` is joined to `[1 : ⋯ : 1]` by a path.**  Pick a chart `i` containing
`p`; the straight segment from `chartFun i p` to `chartFun i [1:⋯:1]` in `ℂⁿ`, read through the
continuous map `chartInv i`, is a path in `ℂPⁿ` from `p` to `[1 : ⋯ : 1]` (`chartInv i` is a left
inverse of `chartFun i` on the chart). -/
theorem joined_allOnesCP (n : ℕ) (p : CP n) : Joined p (allOnesCP n) := by
  obtain ⟨i, hp⟩ := exists_mem_chartSet p
  refine ⟨Path.mk ⟨fun t : unitInterval =>
    chartInv i ((1 - (t:ℝ)) • chartFun i p + (t:ℝ) • chartFun i (allOnesCP n)), ?_⟩ ?_ ?_⟩
  · exact (continuous_chartInv i).comp (by fun_prop)
  · simp only [Set.Icc.coe_zero, sub_zero, one_smul, zero_smul, add_zero]
    exact chartInv_chartFun i p hp
  · simp only [Set.Icc.coe_one, sub_self, zero_smul, one_smul, zero_add]
    exact chartInv_chartFun i (allOnesCP n) (allOnesCP_mem_chartSet i)

theorem pathConnectedSpace_CP (n : ℕ) : PathConnectedSpace (Work.Projective.CP n) := by
  refine ⟨nonempty_CP n, fun p q => ?_⟩
  exact (joined_allOnesCP n p).trans (joined_allOnesCP n q).symm

end

end Work.Projective
