import Mathlib
import Submission.Work.ThompsonFrobenius.GTDefs
import Submission.Work.ThompsonFrobenius.pPrimeCore_eq_bot
import Submission.Work.ThompsonFrobenius.isSolvable
import Submission.Work.ThompsonFrobenius.abelianSylowTwo

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# GT-8: no minimal counterexample exists (area `ThompsonFrobenius`)

Step GT-8 of `NOTES_LEAD_bs_thompson.md`.  `GlaubermanZJProp` applies to `G` (solvable — GT-7a,
abelian Sylow `2` — GT-7b, `p` odd) and gives that `O_{p'}(G)·Z(J(P))` is characteristic in `G`.
By GT-2, `O_{p'}(G) = 1`, so `Z(J(P))` itself is characteristic, hence normal, hence
`N_G(Z(J(P))) = G`; the hypothesis `h.hyp` then makes `G` `p`-nilpotent, contradicting
`h.not_npc`.
-/

set_option autoImplicit false

namespace Work.ThompsonFrobenius

theorem gtMinimal_false (hZJ : Submission.Blueprint.GlaubermanZJProp) {p : ℕ} {G : Type}
    [Group G] [Finite G] {P : Sylow p G} (h : GTMinimal p G P) : False := by
  haveI : Fact p.Prime := ⟨h.prime⟩
  have hchar : (Submission.Blueprint.pPrimeCore p G ⊔
      Submission.Blueprint.ZJ (P : Subgroup G)).Characteristic :=
    hZJ G p h.prime h.ne_two (isSolvable h) (abelianSylowTwo h) P
  have hcharZ : (Submission.Blueprint.ZJ (P : Subgroup G)).Characteristic := by
    rw [pPrimeCore_eq_bot h, bot_sup_eq] at hchar
    exact hchar
  haveI := hcharZ
  have hnorm : Subgroup.normalizer (Submission.Blueprint.ZJ (P : Subgroup G) : Set G) = ⊤ :=
    Subgroup.normalizer_eq_top_iff.mpr
      (inferInstance : (Submission.Blueprint.ZJ (P : Subgroup G)).Normal)
  exact h.not_npc
    (Work.NPC.Basic.hasNormalPComplement_congr Subgroup.topEquiv (hnorm ▸ h.hyp))

end Work.ThompsonFrobenius
