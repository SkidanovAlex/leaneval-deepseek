import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Order.CompletePartialOrder
import Submission.Work.Spaces.Defs
import Submission.Work.Construction.Defs
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.EllipticEst.UopHk.L12_contDiffOn_reg
import Submission.Work.FTS.H2.L12HQ

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.H6Pair6Aux.T5bAux

/-- `L₁₂(f)` is `C¹` on `(0,∞)` for a datum smooth on the open quadrant with
`HkMem α 7 f`.  In fact `UopHk.contDiffOn_L12_k` gives `C⁷`; only order one is needed, so
the statement is weakened with `ContDiffOn.of_le`.  The construction-area operator
`Work.Construction.L12` is the elliptic-area operator `Work.Elliptic.L12`
(`Work.FTS.H2.constructionL12_eq_ellipticL12`). -/
theorem l12ContDiffOnOpen : ∀ α ∈ Set.Ioc 0 1, ∀ f : ℝ → ℝ → ℝ,
    Work.FTS.EllipticEst.SmoothOpen f → Work.Spaces.HkMem α 7 f →
    ContDiffOn ℝ 1 (fun z => Work.Construction.L12 f z) (Set.Ioi 0) := by
  intro α hα f hF hmem
  have h := Work.FTS.EllipticEst.UopHk.contDiffOn_L12_k α 7 f hα.1 hα.2 hF hmem
    (by norm_num)
  rw [Work.FTS.H2.constructionL12_eq_ellipticL12 f]
  exact h.of_le (by norm_num)

end Work.FTS.StrongPersist.H6Pair6Aux.T5bAux
