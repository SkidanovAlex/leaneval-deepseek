import Mathlib
import Submission.Work.Diff.EXT.ladderSrcDefs
import Submission.Work.Diff.EXT.jetSmoothDefs
import Submission.Work.Diff.EXT.ckt_step_tderiv
import Submission.Work.Diff.GE.curv_var_prelim
import Submission.Work.Diff.T.lc_variation
import Submission.Work.Diff.Evol.cv_dLC

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The connection-variation operator of the ladder step (definitions)

`Work.Diff.EXT.evolX.connVarOp G t k` is the connection-variation source of the reaction-ladder step
`(k,j) ← (k-1,j+1)`, written as a packed tensorial operator of arity `k + 5`: the level-`k`
curvature tower with one slot replaced by the first variation `dLC G t` of the Levi-Civita
connection along the flow.  This is the operator whose jets are bounded in
`Work.Diff.EXT.evolX.connVarOp_jets`.

This module only *defines* the operator (and is deliberately free of any dependence on the target
module `Work.Diff.EXT.evolX.connVar_src_jets`, so that lemmas about it can be proved in modules that
the target imports).
-/

set_option linter.unusedSectionVars false

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter

namespace Work.Diff.EXT.evolX

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]

/-- **The connection-variation operator**: the level-`k` curvature tower with one slot replaced by
the first variation of the Levi-Civita connection along the flow, i.e. the pointwise identity
`∑_s ckt (G t) k (update F' s (dLC G t (F 0) (F' s)))`. -/
noncomputable def connVarOp (G : ℝ → Submission.Diff.SMet I M) (t : ℝ) (k : ℕ) :
    (Fin (k + 5) → TField (I := I) (M := M)) → M → ℝ :=
  fun F y => - ∑ s : Fin (k + 4),
      ckt (G t) k (Function.update (fun i : Fin (k + 4) => F i.succ) s
        (Submission.Diff.dLC G t (F 0) ((fun i : Fin (k + 4) => F i.succ) s))) y

end Work.Diff.EXT.evolX
