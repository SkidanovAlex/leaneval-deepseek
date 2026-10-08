import Mathlib
import Submission.Work.CORE3.Defs
import Submission.Work.CORE3.CardInfConjSubOfThree
import Submission.Work.CORE3.BenderSevenU3
import Submission.Work.CORE3.Case1bSeven

namespace Work.CORE3

open Subgroup
open Work.GW2

theorem BenderSevenD6 (G : Type) [Group G] [Finite G] (I : Work.CORE3.Case1Inputs) (h : Work.GW2.BenderCtx G)
    (B : Work.GW2.BenderSetup G) (h1 : Work.GW2.Case1 B) (D : Work.GW2.Case1bData B)
    {y : G} (hy2 : orderOf y = 2) (hyH : y ∉ B.Hhat)
    (X : Subgroup G) (hXle : X ≤ B.Hhat) (hXne : X ≠ ⊥) (hXodd : Odd (Nat.card ↥X))
    (hinv : Work.GW2.Inverts y X)
    (hCeven : Even (Nat.card (Subgroup.centralizer (X : Set G))))
    (hNeven : Even (Nat.card (Subgroup.normalizer (X : Set G)))):
    Nat.card ↥(B.Hhat ⊓ Work.GW2.conjSub y B.Hhat) = 6 := by
  -- Bender's (7), both halves: `|U| = 3` and `cosetInvCount Ĥ y = 4`.
  -- (`card_inf_conjSubOfThree`, used below, now lives in
  -- `Submission/Work/CORE3/CardInfConjSubOfThree.lean`, a module below `Case1bSeven`, so that
  -- `Work.CORE3.Case1bStabTrivial` can cite it without an import cycle.)
  obtain ⟨hU3, hy4⟩ :=
    Case1bSeven G I h B h1 D y hy2 hyH X hXne hXodd hXle hinv hCeven hNeven
  -- conversion of `|U| = 3 ∧ n = 4` into `|Ĥ ⊓ Ĥ^y| = 6`
  exact card_inf_conjSubOfThree I h B h1 D hy2 hyH X hXle hXne hXodd hinv hCeven hNeven hU3 hy4

end Work.CORE3
