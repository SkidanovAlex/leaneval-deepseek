import Mathlib.Analysis.InnerProductSpace.PiL2
import Submission.Work.BoseBoxFock.PCFU.chBslotAux
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseBoxFock.PCFU

theorem latVec_far_tail_sum (u : Finset (Fin 3 → ℤ)) :
    (∑ d ∈ u, if d ∈ Work.BoseBoxFock.PCFU.smLab then 0
      else (‖Work.BoseBoxFock.latVec d‖ - 3 / 2) ^ (-(5 : ℤ))) ≤ 4 ^ 5 * 227 := by sorry

end Work.BoseBoxFock.PCFU
