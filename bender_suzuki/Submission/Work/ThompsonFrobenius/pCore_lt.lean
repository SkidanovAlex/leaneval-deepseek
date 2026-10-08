import Mathlib
import Submission.Work.ThompsonFrobenius.GTDefs
import Submission.Work.ThompsonFrobenius.normalizer_le_normalizer_ZJ
import Submission.Work.HallHigman.ModRep

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# GT-2': `O_p(G) < P` (area `ThompsonFrobenius`)

Step GT-2' of `NOTES_LEAD_bs_thompson.md`.  The normal `p`-subgroup `O_p(G)` lies in every Sylow
`p`-subgroup (`IsPGroup.le_sylow_of_normal`).  If `O_p(G) = P` then `P ⊴ G`, so
`N_G(P) = G` and hence `N_G(ZJ(P)) = G` (`normalizer_le_normalizer_ZJ`); the hypothesis `h.hyp`
then gives a normal `p`-complement of `G` itself, contradicting `h.not_npc`.
-/

set_option autoImplicit false

namespace Work.ThompsonFrobenius

theorem pCore_lt {p : ℕ} {G : Type} [Group G] [Finite G] {P : Sylow p G}
    (h : GTMinimal p G P) : Work.HallHigman.pCore p G < (P : Subgroup G) := by
  haveI : Fact p.Prime := ⟨h.prime⟩
  refine lt_of_le_of_ne (IsPGroup.le_sylow_of_normal Work.HallHigman.isPGroup_pCore P) ?_
  intro heq
  have hPn : (P : Subgroup G).Normal :=
    heq ▸ (inferInstance : (Work.HallHigman.pCore p G).Normal)
  have htop : Subgroup.normalizer (Submission.Blueprint.ZJ (P : Subgroup G) : Set G) = ⊤ := by
    refine le_antisymm le_top ?_
    rw [← Subgroup.normalizer_eq_top_iff.mpr hPn]
    exact normalizer_le_normalizer_ZJ (P : Subgroup G)
  exact h.not_npc
    (Work.NPC.Basic.hasNormalPComplement_congr Subgroup.topEquiv (htop ▸ h.hyp))

end Work.ThompsonFrobenius
