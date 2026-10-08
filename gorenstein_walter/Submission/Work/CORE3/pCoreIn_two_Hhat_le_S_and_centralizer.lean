import Mathlib
import Submission.Work.CORE3.Defs
import Submission.Work.CORE2A.lemma24
import Submission.Work.CORE2A.Basic
import Submission.Work.CORE2A.PcoreInBasic
import Submission.Work.CORE2A.CS_eq_O2_plan

namespace Work.CORE3

theorem pCoreIn_two_Hhat_le_S_and_centralizer {G : Type} [Group G] [Finite G]
    (B : Work.GW2.BenderSetup G) :
    Work.GW2.pCoreIn 2 B.Hhat ≤ (B.S : Subgroup G) ∧
      Work.GW2.pCoreIn 2 B.Hhat ≤ Subgroup.centralizer (B.U : Set G) :=
  ⟨Work.CORE2A.pCoreIn_le_S B, Work.CORE2A.V_le_centralizer_U B⟩

end Work.CORE3
