import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Submission.Work.FTS.PhiStar.Defs
import Submission.Work.FTS.PhiStar.Basic
import Submission.Work.FTS.EllipticEst.TT.WeakDefs
import Submission.Work.Elliptic.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PhiStar

theorem bslOp_sol_exists (k : ℕ) :
    ∀ (α : ℝ) (F : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 / 4 →
      Work.FTS.EllipticEst.SmoothOpen F → Work.Spaces.HkMem α k F →
      (∀ z, 0 < z → Work.Elliptic.Fstar F z = 0) →
      (∀ θ ∈ Work.Spaces.Iθ, Filter.Tendsto (fun z => F z θ) Filter.atTop (nhds 0)) →
      ∃ Ψ : ℝ → ℝ → ℝ,
        Work.FTS.EllipticEst.TT.EllWeakPos α k F Ψ ∧ Work.Elliptic.IsBslSol α F Ψ := by sorry

end Work.FTS.PhiStar
