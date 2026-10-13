import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.InnerProductSpace.Basic
import Submission.Work.FTS.StrongPersist.Clauses

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist

open Work.FTS.Galerkin (Fn Fam slice dynRHS)

set_option autoImplicit false
set_option linter.unusedVariables false

/-- `SmoothOpen` is stable under multiplication by a constant.  (Local helper: the
`ContDiffOn`-instance for `•` is not available in this Mathlib, so the product form is used.) -/
theorem smoothOpen_const_mul' (c : ℝ) {f : ℝ → ℝ → ℝ}
    (hf : Work.FTS.EllipticEst.SmoothOpen f) :
    Work.FTS.EllipticEst.SmoothOpen (fun z θ => c * f z θ) := by
  refine (Work.FTS.EllipticEst.smoothOpen_iff_forall _).mpr (fun n => ?_)
  have h := (Work.FTS.EllipticEst.smoothOpen_iff_forall _).mp hf n
  have h2 : ContDiffOn ℝ n (fun p : ℝ × ℝ => c * Function.uncurry f p)
      Work.FTS.EllipticEst.Q0 := contDiffOn_const.mul h
  exact h2



end Work.FTS.StrongPersist
