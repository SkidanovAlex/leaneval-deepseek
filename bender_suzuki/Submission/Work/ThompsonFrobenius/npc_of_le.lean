import Mathlib
import Submission.Work.ThompsonFrobenius.GTDefs
import Submission.Work.ThompsonFrobenius.ZJ_subgroupOf
import Submission.Work.ThompsonFrobenius.hasNormalPComplement_normalizer_subgroupOf

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# GT-c: every proper subgroup containing `P` is `p`-nilpotent (area `ThompsonFrobenius`)

Step GT-c of `NOTES_LEAD_bs_thompson.md`.  Let `G` be a minimal counterexample to the
Glauberman–Thompson theorem with Sylow `p`-subgroup `P`.  If `P ≤ L < G`, then `L` satisfies the
hypothesis of the theorem for its own Sylow subgroup `P|_L`, hence is `p`-nilpotent by the
induction hypothesis `h.ih`:

* `P|_L := P.subtype hPL` is a Sylow `p`-subgroup of `L`;
* its `ZJ` is `ZJ(P)|_L` (`ZJ_subgroupOf`);
* `N_L(ZJ(P)) = N_G(ZJ(P))|_L`, and `N_G(ZJ(P))` has a normal `p`-complement by `h.hyp`; a
  subgroup of a group with a normal `p`-complement has one
  (`hasNormalPComplement_normalizer_subgroupOf`).
-/

set_option autoImplicit false

namespace Work.ThompsonFrobenius

theorem npc_of_le {p : ℕ} {G : Type} [Group G] [Finite G] {P : Sylow p G}
    (h : GTMinimal p G P) {L : Subgroup G} (hPL : (P : Subgroup G) ≤ L) (hL : L ≠ ⊤) :
    Work.NPC.HasNormalPComplement p ↥L := by
  haveI : Fact p.Prime := ⟨h.prime⟩
  have hcard : Nat.card ↥L < Nat.card G := by
    have hlt := Subgroup.card_lt_of_lt (H := L) (K := ⊤) (lt_top_iff_ne_top.mpr hL)
    rwa [Subgroup.card_top] at hlt
  refine h.ih ↥L hcard (P.subtype hPL) ?_
  have hZ : Submission.Blueprint.ZJ ((P.subtype hPL : Sylow p ↥L) : Subgroup ↥L)
      = (Submission.Blueprint.ZJ (P : Subgroup G)).subgroupOf L := by
    rw [Sylow.coe_subtype, ZJ_subgroupOf hPL]
  rw [hZ]
  exact hasNormalPComplement_normalizer_subgroupOf (le_trans (ZJ_le (P : Subgroup G)) hPL) h.hyp

end Work.ThompsonFrobenius
