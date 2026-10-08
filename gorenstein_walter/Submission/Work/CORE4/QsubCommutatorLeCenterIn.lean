import Mathlib
import Submission.Work.CORE4.Defs
import Submission.Work.CORE4.EightIdxDefs

namespace Work.CORE4

theorem QsubCommutatorLeCenterIn {G : Type} [Group G] [Finite G] (p : ℕ)
    (B : Work.GW2.BenderSetup G) :
    ⁅Work.CORE4.Qsub p B, Work.GW2.pCoreIn p B.U⁆ ≤ Work.CORE4.centerIn (Work.CORE4.Qsub p B) := by sorry

end Work.CORE4
