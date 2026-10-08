import Mathlib
import Submission.Work.BrauerSuzuki.Defs
import Submission.Work.BrauerSuzuki.OddCore.oddCard_oddCore
import Submission.Work.BrauerSuzuki.OddCore.le_of_normal_odd
import Submission.Work.BrauerSuzuki.Sylow.hasFrobeniusCondition_two_of_cyclic_sylow
import Submission.Work.NPC.All

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# The cyclic Sylow `2`-subgroup case of the Brauer–Suzuki reduction

If a finite group `G` has a cyclic Sylow `2`-subgroup `S`, then for **every** involution
`t ∈ G`

  `O(G) · C_G(t) = G`,   i.e.  `oddCore G ⊔ Subgroup.centralizer {t} = ⊤`.

The argument.

* A cyclic Sylow `2`-subgroup forces every `2`-subgroup to be cyclic, hence `G` satisfies
  Frobenius' hypothesis at `p = 2`
  (`Work.BrauerSuzuki.Sylow.hasFrobeniusCondition_two_of_cyclic_sylow`); Frobenius' normal
  `p`-complement theorem (`Work.NPC.frobenius_npc`) then produces a normal `2`-complement
  `N ⊴ G`: `Nat.card N` is coprime to `2` and `G ⧸ N` is a `2`-group.
* `N` is a normal subgroup of odd order, so `N ≤ O(G)`
  (`Work.BrauerSuzuki.OddCore.le_of_normal_odd`).
* By `Work.NPC.Basic.isNormalPComplement_complement_sylow`, `N` is a complement of **any** Sylow
  `2`-subgroup `Q`: `N ⊔ Q = ⊤`.  In particular `O(G) ⊔ Q = ⊤`.
* The involution `t` lies in some Sylow `2`-subgroup `Q` (a group element of `2`-power order lies
  in a Sylow), and `Q` is cyclic (all Sylow `2`-subgroups are conjugate to `S`), hence abelian,
  so `Q ≤ C_G(t)`.  Therefore `O(G) ⊔ C_G(t) ⊇ O(G) ⊔ Q = ⊤`.
-/

set_option linter.style.haveILetI false

namespace Work.BrauerSuzuki.Glue

theorem cyclic_sylow_case {G : Type*} [Group G] [Finite G]
    (S : Sylow 2 G) (hS : IsCyclic ↥S) {t : G} (ht : orderOf t = 2) :
    Submission.Blueprint.oddCore G ⊔ Subgroup.centralizer ({t} : Set G) = ⊤ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  -- Frobenius' condition at `2`, and the resulting normal `2`-complement `N`.
  have hFrob : Work.NPC.HasFrobeniusCondition 2 G :=
    Work.BrauerSuzuki.Sylow.hasFrobeniusCondition_two_of_cyclic_sylow S hS
  obtain ⟨N, hN⟩ := Work.NPC.frobenius_npc (p := 2) hFrob
  have hNnorm : N.Normal := hN.normal
  have hNodd : Odd (Nat.card N) := Nat.coprime_two_right.mp hN.coprime_card
  have hNO : N ≤ Submission.Blueprint.oddCore G :=
    Work.BrauerSuzuki.OddCore.le_of_normal_odd hNnorm hNodd
  -- The involution `t` lies in a Sylow `2`-subgroup `Q`.
  have htP : IsPGroup 2 (Subgroup.zpowers t) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, ht]; norm_num)
  obtain ⟨Q, hQle⟩ := IsPGroup.exists_le_sylow htP
  have htQ : t ∈ (Q : Subgroup G) := hQle (Subgroup.mem_zpowers t)
  have hQcyc : IsCyclic ↥(Q : Subgroup G) :=
    Work.BrauerSuzuki.Sylow.isCyclic_of_isPGroup_two_of_cyclic_sylow S hS (Q : Subgroup G)
      Q.isPGroup'
  -- A cyclic `2`-subgroup is abelian, hence contained in the centralizer of `t ∈ Q`.
  have hQcent : (Q : Subgroup G) ≤ Subgroup.centralizer ({t} : Set G) := by
    haveI : IsCyclic ↥(Q : Subgroup G) := hQcyc
    intro s hs
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff] at hh
    rw [hh]
    have hcomm : (⟨t, htQ⟩ : ↥(Q : Subgroup G)) * ⟨s, hs⟩ = ⟨s, hs⟩ * ⟨t, htQ⟩ :=
      (IsCyclic.isMulCommutative (α := ↥(Q : Subgroup G))).is_comm.comm _ _
    exact congrArg (Subtype.val) hcomm
  -- `N` is a complement of the Sylow `Q`.
  have hbot : N ⊔ (Q : Subgroup G) = ⊤ :=
    (Work.NPC.Basic.isNormalPComplement_complement_sylow hN Q).sup_eq_top
  refine le_antisymm le_top ?_
  rw [← hbot]
  exact sup_le_sup hNO hQcent

end Work.BrauerSuzuki.Glue
