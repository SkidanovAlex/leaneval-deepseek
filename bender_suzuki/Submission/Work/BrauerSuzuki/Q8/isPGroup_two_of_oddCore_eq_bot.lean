import Mathlib
import Submission.Work.NPC.All
import Submission.Work.BrauerSuzuki.OddCore.le_of_normal_odd

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.BrauerSuzuki.Q8

/-- A normal `2`-complement `N` of a finite group `G` has `Nat.card N` coprime to `2`, hence
`N` has odd order, hence `N ≤ O(G)`.  So if `O(G) = ⊥` then `N = ⊥`, and the defining
property that `G ⧸ N` is a `2`-group says exactly that `G` is a `2`-group. -/
theorem isPGroup_two_of_oddCore_eq_bot {G : Type*} [Group G] [Finite G]
    (hO : Submission.Blueprint.oddCore G = ⊥)
    (hN : Work.NPC.HasNormalPComplement 2 G) :
    IsPGroup 2 G := by
  obtain ⟨N, hN⟩ := hN
  haveI := hN.normal
  -- `N` is a normal subgroup of odd order, hence `N ≤ O(G) = ⊥`.
  have hodd : Odd (Nat.card N) := Nat.coprime_two_right.mp hN.coprime_card
  have hle : N ≤ Submission.Blueprint.oddCore G :=
    Work.BrauerSuzuki.OddCore.le_of_normal_odd hN.normal hodd
  have hbot : N = ⊥ := le_bot_iff.mp (hle.trans_eq hO)
  have hq : IsPGroup 2 (G ⧸ N) := hN.isPGroup_quotient
  subst hbot
  exact hq.of_equiv QuotientGroup.quotientBot

end Work.BrauerSuzuki.Q8
