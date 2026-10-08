import Submission.Blueprint.Interfaces

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# Bender–Suzuki blueprint: assembly

The challenge from the area `Prop`s. Only glue lives here: the case split of Peterfalvi II
(Zassenhaus case `V = 1` / `V ≠ 1`), the strong induction on `|G|` behind Theorem B, and the
final call to `Endgame`. The black-box `Prop`s (Brauer–Suzuki, ZJ, Thompson, Higman, Hering,
Feit–Sibley, rank-one uniqueness, Theorem C, Ch. II §4) are consumed by the area theorems, not by
this glue; they are listed in `bender_suzuki_of_areas` so that the final wiring is one
application of each area theorem.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

open LeanEval.GroupTheory.Defs

namespace Submission.Blueprint

/-- The simple case (B0)–(B2) with `O^{2'}(G) = G`: `G` itself is a simple Bender group. -/
theorem simpleCase_of_areas (hR : ReductionsProp) (hA : ThmAProp) (hD : ThmDProp)
    (hZ1 : ZassenhausTwoGroupProp) (hZ2 : ZassenhausPSL2Prop) (hZ3 : ZassenhausSzProp)
    (hF : ThmFProp) (hG : ThmGProp) (hU : PSU3Prop)
    (G : Type) [Group G] [Finite G] (hS : Situation G) (hres : oddResidual G = ⊤) :
    IsSimpleBenderGroup G := by
  obtain ⟨hsimple, -⟩ := (hR G hS.1 hS.2.1).2 hS.2.2 hres
  obtain ⟨hfour, H, hH⟩ := hS.1
  obtain ⟨t, ht, htH, Q, hQH, hQn, hQD, hQD'⟩ := hD G hS H hH
  have hsplit : IsSplitRankOne H Q t := ⟨hH, hA G hfour H hH, ht, htH, hQH, hQn, hQD, hQD'⟩
  by_cases hZ : IsZassenhaus H
  · have h2 := hZ1 G hsimple H Q t hsplit hZ
    by_cases hab : IsAbelianSubgroup Q
    · obtain ⟨n, hn, ⟨e⟩⟩ := hZ2 G hsimple H Q t hsplit hZ h2 hab
      exact .isPSL2 n hn e
    · obtain ⟨n, hn, ⟨e⟩⟩ := hZ3 G hsimple H Q t hsplit hZ h2 hab
      exact .isSuzuki n hn e
  · have hB3 := hF G hS hsimple H Q t hsplit
    have h2 := hG G hS hsimple H Q t hsplit hZ hB3
    obtain ⟨n, hn, ⟨e⟩⟩ := hU G hS hsimple H Q t hsplit hZ hB3 h2
    exact .isPSU3 n hn e

/-- Theorem B by strong induction on `|G|`. -/
theorem theoremB_of_areas (hR : ReductionsProp)
    (hSC : ∀ (G : Type) [Group G] [Finite G], Situation G → oddResidual G = ⊤ →
      IsSimpleBenderGroup G) : TheoremB := by
  have key : ∀ n : ℕ, ∀ (G : Type) [Group G] [Finite G], Nat.card G = n → BenderHyp G →
      BenderConclusion G := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro G _ _ hn hB
      have hBelow : ThmBBelow (Nat.card G) := fun F _ _ hlt hF => ih _ (hn ▸ hlt) F rfl hF
      by_cases h : oddCore G = ⊥ ∧ oddResidual G = ⊤
      · exact ((hR G hB hBelow).2 h.1 h.2).2 (hSC G ⟨hB, hBelow, h.1⟩ h.2)
      · refine (hR G hB hBelow).1 ?_
        by_contra hc
        exact h ⟨not_not.mp fun h' => hc (Or.inl h'), not_not.mp fun h' => hc (Or.inr h')⟩
  intro G _ _ hB
  exact key _ G rfl hB

/-- **The Bender–Suzuki theorem from the areas.** `hFT` and the black-box `Prop`s are consumed
by the area theorems (each area theorem has the shape `theorem X (hFT : FeitThompsonProp)
(h… : …Prop) : XProp`); the glue above uses the rest. -/
theorem bender_suzuki_of_areas.{u} (hFT : FeitThompsonProp)
    -- black boxes
    (hBrSz : BrauerSuzukiProp) (hZJ : GlaubermanZJProp) (hTh : ThompsonFrobeniusProp)
    (hHig : HigmanProp) (hHer : HeringProp) (hFS : FeitSibleyProp)
    (hR1 : RankOneUniquenessProp) (hMod : ModelFactsProp)
    -- Bender (Peterfalvi I)
    (hA : ThmAProp) (hRed : ReductionsProp) (hC : ThmCProp) (hC4 : ChIIFourProp)
    (hD : ThmDProp)
    -- Suzuki (Peterfalvi II) and Zassenhaus groups
    (hZ1 : ZassenhausTwoGroupProp) (hZ2 : ZassenhausPSL2Prop) (hZ3 : ZassenhausSzProp)
    (hF : ThmFProp) (hG : ThmGProp) (hU : PSU3Prop)
    -- endgame
    (hE : EndgameProp.{u})
    {X : Type u} [Group X] [Finite X] [IsSimpleGroup X]
    (M : Subgroup X) (h : IsStronglyEmbedded M) :
    IsSimpleBenderGroup X :=
  hE (theoremB_of_areas hRed (simpleCase_of_areas hRed hA hD hZ1 hZ2 hZ3 hF hG hU))
    hBrSz hMod X M h

end Submission.Blueprint
