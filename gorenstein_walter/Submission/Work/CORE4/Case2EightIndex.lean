import Mathlib
import Submission.Work.CORE4.Defs
import Submission.Work.CORE4.API

namespace Work.CORE4

/-- Bender 1981, §4 (8), the index bound `|U : B₀ K F(U)| ≤ p`: for every prime `p` and every
`P ≤ D.F` of order `p`, the odd core `U = O(H)` satisfies
`(D.B0 ⊔ D.K ⊔ F(U)).relIndex U ≤ p`. -/
theorem Case2EightIndex (I : Work.GW2.C4Inputs) :
    ∀ (G : Type) [Group G] [Finite G], Work.GW2.BenderCtx G → ∀ B : Work.GW2.BenderSetup G,
      Work.GW2.Case2 B → ∀ C : Work.GW2.Case2Ctx6 B, Work.GW2.Case2PrePlus B C.D →
        Work.GW2.Case2SevenFacts B C.D →
        ∀ (p : ℕ) (P : Subgroup G), p.Prime → P ≤ C.D.F → Nat.card P = p →
          (C.D.B0 ⊔ C.D.K ⊔ Work.GW2.fittingIn B.U).relIndex B.U ≤ p := by sorry

end Work.CORE4
