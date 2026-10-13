import Mathlib.Basic.Real.Basic
import Submission.Work.FTS.TransportS.Slots
import Submission.Work.FTS.TransportS.T2Sup.Final
import Submission.Work.FTS.TransportS.T2Sup.slotAbsBound

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.TransportS

/-- **The per-slot transport bound `T2Slot`.**  This is the frozen statement of
`Submission/Work/FTS/TransportS/Slots.lean`.

The proof is the weighted per-slot estimate `T2Sup.slotAbsBound` (the `canonW q`-weighted
version of the same bound, covering all three leaf exponents `q ∈ {0, η, γ}` at once), together
with the reduction `T2Sup.T2Slot_of_slotAbs` that identifies the leaf weights of `IP4` with the
canonical weights `canonW 0`, `canonW η` and `canonW γ` (`Slots.leafEta`, `Slots.leafOne`,
`Slots.leafGam`). -/
theorem t2SlotGuarded : ∃ C : ℝ, 0 < C ∧ Work.FTS.TransportS.T2Slot C :=
  Work.FTS.TransportS.T2Sup.T2Slot_of_slotAbs
    (show Work.FTS.TransportS.T2Sup.SlotAbsProp from
      Work.FTS.TransportS.T2Sup.slotAbsBound Work.FTS.TransportS.T2Sup.delicateBound)

end Work.FTS.TransportS
