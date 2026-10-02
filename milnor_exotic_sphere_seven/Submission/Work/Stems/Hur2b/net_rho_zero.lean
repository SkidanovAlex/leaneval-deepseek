import Mathlib
import Submission.Work.Stems.Hur2b.NetTree

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

namespace Work.Stems.Hur2b

/-- At time `0` the contraction `rho` is the folding `prune` at time `0`, which fixes the tree. -/
theorem net_rho_zero {p : Work.Stems.Cubical.IC 3} (h : Work.Stems.Hur2b.Tree p) :
    Work.Stems.Hur2b.rho 0 p = p := by
  rw [rho, if_pos (by norm_num : (0 : ℝ) ≤ 1 / 5)]
  rw [show (5 : ℝ) * 0 = 0 by norm_num]
  exact prune_zero h

end Work.Stems.Hur2b
