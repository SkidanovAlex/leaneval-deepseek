import Mathlib
import Submission.Work.CORE4.Case2PerXBound9
import Submission.Work.CORE4.Case2CountAssembly
import Submission.Work.CORE4.Case2Fibre9
import Submission.Work.CORE4.Case2CentA
import Submission.Work.CORE4.Case2CentCard
import Submission.Work.CORE4.Case2NormalizerP
import Submission.Work.CORE4.L2NormTwoE
import Submission.Work.CORE4.L2TorusNormE

namespace Work.CORE4.Counting

theorem PerXAmalgamCount (I : Work.GW2.C4Inputs) :
    ∀ (G : Type) [Group G] [Finite G], Work.GW2.BenderCtx G →
      ∀ (B : Work.GW2.BenderSetup G) (h : Work.GW2.Case2Ctx B), Work.GW2.Case2 B →
        Work.GW2.Case2PrePlus B h.D → Work.GW2.Case2SevenFacts B h.D →
        Work.GW2.Case2EightAll B h.D →
        ∀ (p : ℕ) (P A : Subgroup G),
          p.Prime → P ≤ h.D.F → Nat.card ↥P = p → Work.GW2.Case2EightObj h.D p P A →
          (Work.CORE4.inConjSet P (Work.GW2.layerIn h.D.M)).ncard =
              (Work.GW2.Case2EightP1 P A - 1) * (h.D.M ⊓ B.H).relIndex h.D.M + 1 →
          ∀ g : G, Work.GW2.conjSub g P ≠ P → Work.GW2.conjSub g P ≤ A →
            {Y : Subgroup G | (∃ Z ∈ Work.CORE4.inConjSet P (Work.GW2.layerIn h.D.M),
                  Y = Work.GW2.conjSub g Z) ∧
                Y ∉ Work.CORE4.inConjSet P (Work.GW2.layerIn h.D.M) ∧
                ∃ Z ∈ Work.CORE4.inConjSet P (Work.GW2.layerIn h.D.M),
                  Z ≠ Work.GW2.conjSub g P ∧ Y ≤ Subgroup.centralizer (Z : Set G)}.ncard ≤
              ((Work.CORE4.qOf h - 1) * Work.CORE4.qOf h) / p := by sorry

end Work.CORE4.Counting
