import Mathlib
import Submission.Work.Serre.ratPairInputs
import Submission.Work.Serre.ratPairBasic
import Submission.Work.Serre.CWModel.Tower
import Submission.Work.Serre.RatTower.Tower

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

namespace Work.Serre

/-- **The cellular induction over the CW model of the base, over `ℚ`.**

From the sharp rational cell step `RatCellStepSharp`, the comparison map of the pullback of a Serre
fibration `p : E → B` along the `k`-th stage of the model tower
`Work.Serre.CWModel.towerA B b₀ b hb hconn k` is an isomorphism on rational homology below `b + f`
and surjective in degree `b + f`, where `B` is `(b-1)`-connected (`b ≥ 2`) and the fibres of `p` are
rationally acyclic in degrees `0 < j < f` and rationally connected.  This is the tower induction of
`Work.Serre.RatTowerComparison`: the base case is `Work.Serre.RatTower.rt_baseGood` and the step is
`Work.Serre.RatTower.attachStepQ` (one cell attachment, handled by the middle five lemma
`Work.Serre.RatTower.fiveLemmaTau2` applied to the triple sequences of the pair). -/
theorem ratTowerComparison : Work.Serre.RatTowerComparison := by
  intro hcell E B _ _ p hp b₀ b f hb hconn hfib h0 k
  exact Work.Serre.RatTower.rt_goodQ_towerA hcell p hp b₀ b f hb hconn hfib h0 k

end Work.Serre
