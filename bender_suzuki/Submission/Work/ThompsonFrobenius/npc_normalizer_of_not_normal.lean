import Mathlib
import Submission.Work.ThompsonFrobenius.GTDefs
import Submission.Work.ThompsonFrobenius.npc_of_le

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# GT-d: a non-normal `p`-subgroup normalised by `P` has `p`-nilpotent normaliser

Step GT-d of `NOTES_LEAD_bs_thompson.md`.  Let `G` be a minimal counterexample to the
Glauberman–Thompson theorem with Sylow `p`-subgroup `P`, and let `W` be a `p`-subgroup with
`P ≤ N_G(W)`.  If `W` is not normal in `G`, then `N_G(W) ≠ G`
(`Subgroup.normalizer_eq_top_iff`), so `N_G(W)` is a proper subgroup containing `P` and is
`p`-nilpotent by GT-c (`npc_of_le`).
-/

set_option autoImplicit false

namespace Work.ThompsonFrobenius

theorem npc_normalizer_of_not_normal {p : ℕ} {G : Type} [Group G] [Finite G] {P : Sylow p G}
    (h : GTMinimal p G P) {W : Subgroup G}
    (hW : IsPGroup p W) (hPW : (P : Subgroup G) ≤ Subgroup.normalizer (W : Set G))
    (hWn : ¬ W.Normal) :
    Work.NPC.HasNormalPComplement p ↥(Subgroup.normalizer (W : Set G)) := by
  refine npc_of_le h hPW ?_
  intro htop
  exact hWn (Subgroup.normalizer_eq_top_iff.mp htop)

end Work.ThompsonFrobenius
