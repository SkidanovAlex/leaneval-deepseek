import Mathlib
import Submission.Work.Diff.EXT.evolX.opJetSmooth_lapOpE
import Submission.Work.Diff.EXT.curvNormK_frame_indep
import Submission.Work.Diff.EXT.evolX.jetCalcDefs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# `JetSmoothOp` for the curvature tower

`Work.Diff.EXT.JetSmoothOp g K S x` (the workspace's regularity predicate for packed operators,
`Submission/Work/Diff/EXT/jetSmoothDefs.lean`) is the hypothesis under which `jetAll` is *linear* in
the operator (`Work.Diff.EXT.jetAll_sub_of_JetSmoothOp`).  It is required, for instance, by the
general contraction bound `Work.Diff.EXT.evolX.substOp_jets_le_v2` (`hTs`) and by the product bound
`Work.Diff.EXT.evolX.mulOp_jets_le_v2` (`hAs`).

Here we discharge it for the most important operator of the package, the curvature tower
`Work.Diff.EXT.ckt g K = ∇^K Rm` (arity `K + 4`), for an *arbitrary* Riemannian metric `g`.

The proof is the same three-step argument as for the frame trace
(`Work.Diff.EXT.evolX.cvTr0ρ_jetSmoothOp`):

* the level-`0` operator `F ↦ ckt g K F` is `C^∞` on tuples of smooth fields
  (`Work.Diff.EXT.tensProp_all`, component 1);
* hence *all* of its `jetAll`-jets are `C^∞` on such tuples
  (`Work.Diff.EXT.evolX.jetAll_contMDiff_of_base`), which is exactly `JetSmoothOp` up to replacing
  `C^∞` by `MDifferentiableAt`.
-/

set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter

namespace Work.Diff.EXT.evolX

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]

/-- **All the jets of the curvature tower are mdifferentiable**: the packed operator
`Work.Diff.EXT.ckt g K` satisfies `Work.Diff.EXT.JetSmoothOp` at every point. -/
theorem jetSmoothOp_ckt [T2Space M] (hLC : Submission.Diff.LCSmooth I M)
    (g : Submission.Diff.SMet I M) (x : M) (K : ℕ) :
    Work.Diff.EXT.JetSmoothOp (I := I) (M := M) g (K + 4)
      (Work.Diff.EXT.ckt (I := I) (M := M) g K) x := by
  refine Filter.Eventually.of_forall fun y => ?_
  intro l F hF
  exact (Work.Diff.EXT.evolX.jetAll_contMDiff_of_base (I := I) (M := M) hLC g
    (K := K + 4) (S := Work.Diff.EXT.ckt (I := I) (M := M) g K)
    (fun F hF => (Work.Diff.EXT.tensProp_all (I := I) (M := M) hLC g K F hF).1)
    l F hF).contMDiffAt.mdifferentiableAt (by simp)

end Work.Diff.EXT.evolX
