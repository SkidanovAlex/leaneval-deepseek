import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.BoseFixR.PotSplitDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseFixR

open Submission.BoseGases

theorem CombBlockSplit {k j : ℕ} (z : Submission.BoseGases.X k) (y : Submission.BoseGases.X j) :
    Submission.BoseGases.blockSplitEquiv k j (Work.BoseFixR.comb z y) = (z, y) := by
  rw [Submission.BoseGases.blockSplitEquiv_apply]
  refine Prod.ext ?_ ?_
  · funext i
    simp [Work.BoseFixR.comb, Submission.BoseGases.firstBlock]
  · funext i
    simp [Work.BoseFixR.comb, Submission.BoseGases.lastBlock]

end Work.BoseFixR
