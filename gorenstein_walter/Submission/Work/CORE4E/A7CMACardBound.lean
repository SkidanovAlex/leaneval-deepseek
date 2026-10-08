import Mathlib
import Submission.Work.CORE4.Defs
import Submission.Work.CORE4.Defs10
import Submission.Work.AUTA7.A7.CentralizerOrderThree
import Submission.Work.CORE4.A7M_eq
import Submission.Work.CORE4.A7K
import Submission.Work.CORE4.LayerCtx6
import Submission.Work.CORE4.DihOrCycSub

namespace Work.CORE4E

theorem A7CMACardBound (I : Work.GW2.C4Inputs) :
    ∀ (G : Type) [Group G] [Finite G] (B : Work.GW2.BenderSetup G) (C : Work.GW2.Case2Ctx6 B),
      Work.GW2.Hyp9 G B C → Work.GW2.IsA7Case C.D → Work.GW2.A7Facts1 C.D →
        Work.GW2.A7Facts2 B C.D → Work.GW2.A7Facts3 B C.D → Work.GW2.A7Facts5 B C.D →
          Nat.card ↥(C.D.M ⊓ Subgroup.centralizer ((C.D.F ⊔ C.D.K : Subgroup G) : Set G)) ≤ 108 := by
  sorry

end Work.CORE4E
