import Mathlib
import Submission.Work.ThompsonFrobenius.GTDefs
import Submission.Work.ThompsonFrobenius.npc_of_le
import Submission.Work.ThompsonFrobenius.pCore_lt
import Submission.Work.ThompsonFrobenius.centralizer_pCore_le
import Submission.Work.ThompsonFrobenius.Prelim

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# GT-5: `P` is a maximal subgroup of `G` (area `ThompsonFrobenius`)

Step GT-5 of `NOTES_LEAD_bs_thompson.md` (Farris §3.4 Step Four, first half).  Let `G` be the
minimal counterexample and `P ≤ L ≤ G`.  If `L = G` we are done; otherwise GT-c makes `↥L`
`p`-nilpotent, with normal `p`-complement `M ≤ ↥L`.

* If `M = 1` then `L` is a `p`-group containing the Sylow `P`, so `L = P`.
* If `M ≠ 1`, then inside `↥L` the subgroups `M` and `H_L = O_p(G) ∩ L` are normal with coprime
  orders, so `⁅M, H_L⁆ = 1`; hence `M ≤ C_{↥L}(H_L)`, i.e. `M` (as a subgroup of `G`) lies in
  `C_G(O_p(G)) ≤ O_p(G)` (GT-4) — contradicting `M ⊓ H_L = 1` and `M ≠ 1`.
-/

set_option autoImplicit false

open scoped Pointwise commutatorElement

namespace Work.ThompsonFrobenius

theorem eq_of_le {p : ℕ} {G : Type} [Group G] [Finite G] {P : Sylow p G}
    (h : GTMinimal p G P) {L : Subgroup G} (hPL : (P : Subgroup G) ≤ L) :
    L = (P : Subgroup G) ∨ L = ⊤ := by
  haveI : Fact p.Prime := ⟨h.prime⟩
  by_cases hL : L = ⊤
  · exact Or.inr hL
  · left
    let H : Subgroup G := Work.HallHigman.pCore p G
    have hHpg : IsPGroup p H := Work.HallHigman.isPGroup_pCore
    have hHnormal : H.Normal := inferInstance
    have hHlt : H < (P : Subgroup G) := pCore_lt h
    have hHL : H ≤ L := hHlt.le.trans hPL
    obtain ⟨M, hM⟩ := npc_of_le h hPL hL
    by_cases hMbot : M = ⊥
    · have hLpg : IsPGroup p ↥L := by
        rw [hMbot] at hM
        exact IsPGroup.of_equiv hM.isPGroup_quotient (QuotientGroup.quotientBot)
      exact (Subgroup.eq_of_le_of_card_ge hPL (card_le_card_sylow_of_isPGroup hLpg P)).symm
    · exfalso
      haveI hMnormal : M.Normal := hM.normal
      -- the copy of `O_p(G)` inside `↥L`
      let HL : Subgroup ↥L := H.subgroupOf L
      haveI hHLnormal : HL.Normal := Subgroup.normal_comap _
      have hHLcard : Nat.card ↥HL = Nat.card ↥H :=
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hHL).toEquiv
      have hinf : M ⊓ HL = ⊥ := by
        refine Subgroup.inf_eq_bot_of_coprime ?_
        obtain ⟨k, hk⟩ := hHpg.exists_card_eq
        rw [hHLcard, hk]
        exact hM.coprime_card.pow_right k
      -- `M` centralises `O_p(G)` inside `↥L`
      have hcomm : ⁅M, HL⁆ = ⊥ :=
        le_bot_iff.mp ((Subgroup.commutator_le_inf M HL).trans (le_of_eq hinf))
      have hMcent : M ≤ Subgroup.centralizer (HL : Set ↥L) :=
        Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm
      -- hence `M ≤ C_G(O_p(G)) ≤ O_p(G)`, contradicting `M ⊓ H = 1`
      have hMGleC : M.map L.subtype ≤ Subgroup.centralizer (H : Set G) := by
        intro m hm
        obtain ⟨m₀, hm₀, rfl⟩ := Subgroup.mem_map.mp hm
        refine Subgroup.mem_centralizer_iff.mpr ?_
        intro g hg
        have hg' : (⟨g, hHL hg⟩ : ↥L) ∈ HL := hg
        have h1 := Subgroup.mem_centralizer_iff.mp (hMcent hm₀) ⟨g, hHL hg⟩ hg'
        exact congrArg Subtype.val h1
      have hHinf : H ⊓ M.map L.subtype = ⊥ := by
        refine Subgroup.inf_eq_bot_of_coprime ?_
        rw [Subgroup.card_map_of_injective L.subtype_injective]
        obtain ⟨k, hk⟩ := hHpg.exists_card_eq
        rw [hk]
        exact hM.coprime_card.symm.pow_left k
      have hMGbot : M.map L.subtype = ⊥ := by
        have h1 : M.map L.subtype ≤ H := hMGleC.trans (centralizer_pCore_le h)
        have h2 : M.map L.subtype = H ⊓ M.map L.subtype := (inf_eq_right.mpr h1).symm
        rw [h2, hHinf]
      refine hMbot (le_bot_iff.mp ?_)
      have h2 : M ≤ L.subtype.ker := (Subgroup.map_eq_bot_iff M).mp hMGbot
      rwa [Subgroup.ker_subtype] at h2

end Work.ThompsonFrobenius
