import Mathlib
import Submission.Work.CORE4.Defs
import Submission.Work.CORE4.EightIdxDefs

namespace Work.CORE4

theorem CtxCase3InvNormal (I : Work.GW2.C4Inputs) :
    ∀ (G : Type) [Group G] [Finite G], Work.GW2.BenderCtx G →
      ∀ (B : Work.GW2.BenderSetup G) (h : Work.GW2.Case2Ctx B),
        ∀ (p : ℕ) (P A : Subgroup G), p.Prime → P ≤ h.D.F → Nat.card P = p →
          Work.GW2.Case2EightObj h.D p P A →
          ¬ IsCyclic ↥(Work.CORE4.Qsub p B) →
          (∀ x ∈ Work.CORE4.Qsub p B, h.D.s * x * h.D.s⁻¹ = x⁻¹) →
          Work.GW2.Case2InvNormal B h.D := by sorry

end Work.CORE4
