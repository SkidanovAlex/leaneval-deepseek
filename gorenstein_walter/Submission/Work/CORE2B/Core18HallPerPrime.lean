import Mathlib
import Submission.Work.CORE2B.Core18HallPerPrimeCase2

/-!
# GW design 18, item A′: `HallPerPrime` (exact signature of `Work.CORE2B.HallPerPrime`), proved
from `Core18HallPerPrimeCase2`.
-/

namespace Work.GW18

open Subgroup Work.CORE2B

theorem Core18HallPerPrime (T : Work.GW2.LocalToolkit) (h26 : Work.GW2.Thm26Prop)
    (h27 : Work.GW2.Lemma27Prop) (h28 : Work.GW2.Lemma28Prop) (G : Type) [Group G] [Finite G]
    (hFT : Work.GW2.FeitThompsonProp) (hCtx : Work.GW2.BenderCtx G)
    (B : Work.GW2.BenderSetup G) (hnot1 : ¬ Work.GW2.Case1 B) (hnot2 : ¬ Work.GW2.Case2 B)
    (s : G) (hs : s ∈ (B.S : Subgroup G)) (hs0 : s ∉ B.S0) :
    ∀ p : ℕ, Nat.Prime p →
      Work.GW2.pCoreIn p B.U ≤ Subgroup.centralizer ({s} : Set G) ∨
      Work.GW2.pCoreIn p B.U ⊓ Subgroup.centralizer ({s} : Set G) = ⊥ := by
  intro p hp
  by_cases hle : Work.GW2.pCoreIn p B.U ≤ Subgroup.centralizer ({s} : Set G)
  · exact Or.inl hle
  · by_cases hbot : Work.GW2.pCoreIn p B.U ⊓ Subgroup.centralizer ({s} : Set G) = ⊥
    · exact Or.inr hbot
    · exact absurd (Core18HallPerPrimeCase2 T h26 h27 h28 G hFT hCtx B hnot1 hnot2 s hs hs0 p hp
        hbot hle) hnot2

end Work.GW18
