import Mathlib.Analysis.Complex.Trigonometric
import Submission.Work.FTS.EllipticEst.Defs
import Submission.Work.Elliptic.Defs
import Submission.Work.FTS.EllipticEst.TT.L12Moment

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.TT

theorem L12Sin_mem (k : ℕ) : ∀ (α : ℝ) (F Ψ : ℝ → ℝ → ℝ),
    0 < α → α ≤ 1 / 4 → Work.FTS.EllipticEst.EllHyp α k F Ψ →
    Work.Spaces.HkMem α k (fun z θ => Work.Elliptic.L12 F z * Real.sin (2 * θ)) :=
  Work.FTS.EllipticEst.TTL12M.L12Sin_mem_aux k

end Work.FTS.EllipticEst.TT
