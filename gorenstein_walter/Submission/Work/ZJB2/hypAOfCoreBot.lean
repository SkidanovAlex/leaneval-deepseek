import Mathlib
import Submission.Work.ZJB2.Defs
import Submission.Work.GLUE.PcoreApi
import Submission.Work.ZJB2.sylowNeBotOfExists
import Submission.Work.ZJB2.zsNeBotOfIsPGroup
import Submission.Work.ZJB2.normalizerNeTopOfPGroupBot

/-!
# GW design 17, item B (ZJB2) — leaf `hypAOfCoreBot` (B.hypA)

Source: Glauberman 1968, p. 1125 ("By Theorem 5.1 (a), we may assume that `O_p(G) ≠ 1`").

`Work.ZJB.HypAOfCoreBotProp p G` says: if `O_p(G) = 1`, if `(C_p)` holds in every proper
subgroup of `G`, and if `G` has a nontrivial Sylow `p`-subgroup, then hypothesis (a) of
Theorem 5.1 holds, i.e. `(C_p)` holds in `N_G(H)` for every `H` with `Z(S₂) ≤ H ≤ S₂`.

The mathematics (all inside `G`; `p` a prime, `G` finite):

* all Sylow `p`-subgroups of `G` have order `p ^ ν_p(|G|)` (`Sylow.card_eq_multiplicity`),
  so the existence of one nontrivial Sylow `p`-subgroup forces `S₂ ≠ 1`
  (`Work.ZJB2.sylowNeBotOfExists`);
* a nontrivial finite `p`-group has nontrivial centre (`IsPGroup.center_nontrivial`), so
  `Z(S₂) ≠ 1` (`Work.ZJB2.zsNeBotOfIsPGroup`), and `1 ≠ Z(S₂) ≤ H` gives `H ≠ 1`;
* if `N_G(H) = G` then `H ⊴ G` (`Subgroup.normalizer_eq_top_iff`); as `H ≤ S₂` is a
  nontrivial `p`-group, `H ≤ O_p(G) = 1` (the universal property of `O_p(G)`,
  `Work.GW2.le_pCore_of_normal_isPGroup`), a contradiction.  Hence `N_G(H) < G`
  (`Work.ZJB2.normalizerNeTopOfPGroupBot`) and `(C_p)` for the proper subgroup `N_G(H)` —
  the induction hypothesis — is exactly the goal.

This file is the assembly: the three auxiliary facts are the separately proved leaves named
above, and the argument below only combines them.
-/

namespace Work.ZJB2

open Work.GW2 Subgroup

/-- **B.hypA.**  If `O_p(G) = 1`, if `(C_p)` holds in every proper subgroup of `G`, and if
`G` has a nontrivial Sylow `p`-subgroup, then hypothesis (a) of Theorem 5.1 holds: for every
Sylow `p`-subgroup `S₂` and every `H` with `Z(S₂) ≤ H ≤ S₂`, the subgroup `N_G(H)` is proper
and hence satisfies `(C_p)` by the induction hypothesis. -/
theorem hypAOfCoreBot (p : ℕ) [Fact p.Prime] (G : Type) [Group G] [Finite G] :
    Work.ZJB.HypAOfCoreBotProp p G := by
  intro hcore hCp hex S₂ H hZH hHS
  -- Step 1: all Sylow `p`-subgroups of a finite group have the same order, so the Sylow
  -- subgroup `S₂` is nontrivial as soon as one Sylow subgroup is.
  have hS₂ : (S₂ : Subgroup G) ≠ ⊥ := sylowNeBotOfExists p G hex S₂
  -- Step 2: the centre of the nontrivial `p`-group `S₂` is nontrivial.
  have hZne : Work.ZJB.ZS (S₂ : Subgroup G) ≠ ⊥ :=
    zsNeBotOfIsPGroup G (S₂ : Subgroup G) S₂.isPGroup' hS₂
  -- Step 3: `1 ≠ Z(S₂) ≤ H`, so `H ≠ 1`; and `H ≤ S₂` is a `p`-group.
  have hHne : H ≠ ⊥ := fun h => hZne (le_bot_iff.mp (h ▸ hZH))
  have hHp : IsPGroup p ↥H := S₂.isPGroup'.to_le hHS
  -- Step 4: `N_G(H) < G`, else `H ⊴ G` is a nontrivial normal `p`-subgroup and so lies in
  -- `O_p(G) = 1`.
  have hNne : Subgroup.normalizer (H : Set G) ≠ ⊤ :=
    normalizerNeTopOfPGroupBot p G hcore H hHne hHp
  -- Conclusion: `(C_p)` in the proper subgroup `N_G(H)` is exactly the induction hypothesis.
  exact hCp (Subgroup.normalizer (H : Set G)) hNne

end Work.ZJB2
