import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.Vocab
import Submission.Work.FTS.PhiStar.ThetaTraces

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `PhiStar.thetaTraces_of_bdryTraces` (lead install R6, 2026-10-11)

`BdryTraces α k F` implies its θ-part `ThetaTraces α k F` (at `(a,b) = (0,s)`).
-/

namespace Work.FTS.PhiStar

theorem thetaTraces_of_bdryTraces {α : ℝ} {k : ℕ} {F : ℝ → ℝ → ℝ}
    (h : Work.FTS.Nonlin.BdryTraces α k F) : ThetaTraces α k F :=
  fun s hs z hz => (h 0 s (by omega)).2 z hz

end Work.FTS.PhiStar
