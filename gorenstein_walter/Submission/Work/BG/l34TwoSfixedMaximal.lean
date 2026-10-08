import Mathlib
import Submission.Work.BG.ThmABCCharDefs
import Submission.Work.BG.S02
import Submission.Work.BG.thm32
import Submission.Work.BG.lemma33Case2
import Submission.Work.BG.lemma33Leaf

namespace Work.BG

open OddOrder.RepresentationTheory Work.GW2 Work.BG Work.GW2.C16 in
theorem l34TwoSfixedMaximal {G : Type} [Group G] [Finite G] [Fintype G] [Invertible (Nat.card G : ℂ)]
    (D : Work.GW2.BGData G) (C : Work.BG.Sec2Ctx G) [Invertible (Nat.card ↥C.P.H0 : ℂ)] :
    Work.GW2.C16.Compat D C → Work.GW2.C16.Sec3Hyp D → 4 ≤ D.n →
    ∀ f : ClassFunction ↥C.P.H0 ℂ → ClassFunction G ℂ, Work.GW2.C16.IsCoherent C f →
    ∀ χ : ClassFunction G ℂ, Work.BG.IsPmIrr χ →
    ∀ ν₁ ∈ Work.GW2.C16.bset C f χ, ∀ ν₂ ∈ Work.GW2.C16.bset C f χ, ν₁ ≠ ν₂ →
    Work.BG.sconj C ν₁ = ν₁ → Work.BG.sconj C ν₂ = ν₂ →
    (Work.BG.lamOrbit C ν₁).ncard = D.n → (Work.BG.lamOrbit C ν₂).ncard = D.n → False := by
  intro hDC hS3 hn f hf χ hχ ν₁ hν₁ ν₂ hν₂ hne hs1 hs2 ho1 ho2
  have h := lemma33Leaf D C hDC hS3 f hf χ hχ ν₁ hν₁ ν₂ hν₂ hne hs1 hs2 ho1 ho2
  omega

end Work.BG
