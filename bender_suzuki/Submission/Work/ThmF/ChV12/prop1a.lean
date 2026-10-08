import Mathlib
import Submission.Work.ThmF.Setup
import Submission.Work.ThmF.Bender.Basic
import Submission.Work.ThmG.centralizer_le_twoPoint_of_fixedPts_card_two

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.ThmF.ChV12

open LeanEval.GroupTheory.Defs Submission.Blueprint Work.ThmF in theorem prop1a {G : Type} [Group G] [Finite G] (hS : Situation G) (hC4 : ChIIFourProp) (H Q : Subgroup G) (t : G) (h : IsSplitRankOne H Q t) : ∀ x ∈ Kset H t, x ≠ 1 → ∀ q ∈ Q, q * x = x * q → q = 1 := by
  intro x hxK hx1 q hq hqx
  -- Ch. II §4 Prop. 2 (c): `x ∈ K - {1}` fixes exactly two points of `Ω = G ⧸ H`.
  have hfix : (fixedPts H (Subgroup.zpowers x)).ncard = 2 :=
    (hC4 G hS H h.stronglyEmbedded t h.invol h.not_mem).2.2.1 x hxK hx1
  -- Hence every element of `H` centralising `x` lies in `D = H ∩ H^t`.
  have hcH : Subgroup.centralizer ({x} : Set G) ⊓ H ≤ twoPoint H t :=
    Work.ThmG.centralizer_le_twoPoint_of_fixedPts_card_two (Kset_subset H t hxK) hx1 hfix
  -- `q ∈ Q ≤ H` commutes with `x`, so `q ∈ D`; but `Q ⊓ D = 1`.
  have hqD : q ∈ twoPoint H t :=
    hcH ⟨Subgroup.mem_centralizer_singleton_iff.mpr hqx, h.le hq⟩
  have hqbot : q ∈ (⊥ : Subgroup G) := by
    have hmem : q ∈ Q ⊓ twoPoint H t := ⟨hq, hqD⟩
    rwa [h.inf_eq] at hmem
  exact Subgroup.mem_bot.mp hqbot

end Work.ThmF.ChV12
