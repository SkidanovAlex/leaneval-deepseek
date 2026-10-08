/-
Area A9: **Frobenius' normal `p`-complement theorem, local (normalizer) form** — formulation
(3) ⟹ (2).

If for every non-identity `p`-subgroup `Q ≤ G` the normalizer `N_G(Q)` has a normal `p`-complement,
then so does `G` (the converse is `Work.NPC.Basic.hasNormalPComplement_mono`).

This is the third equivalent formulation listed for Frobenius' theorem (see `NOTES.md`).  The proof
composes (3) ⟹ (4) — if `N_G(Q)` has a normal `p`-complement `M`, then `[M,Q] ≤ M ∩ Q = 1`, so
`N_G(Q)/C_G(Q)` is a quotient of the `p`-group `N_G(Q)/M` (proved in
`hasFrobeniusCondition_of_normalizer_npc`) — with (4) ⟹ (2), which is `frobenius_npc`.
-/
import Mathlib
import Submission.Work.NPC.Defs
import Submission.Work.NPC.Frobenius.hasFrobeniusCondition_of_normalizer_npc
import Submission.Work.NPC.Frobenius.frobenius_npc

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.NPC.Frobenius

theorem npc_of_normalizer_npc {G : Type*} [Group G] [Finite G] {p : ℕ} (hp : p.Prime)
    (h : ∀ Q : Subgroup G, IsPGroup p Q → Q ≠ ⊥ →
      Work.NPC.HasNormalPComplement p ↥(Subgroup.normalizer (Q : Set G))) :
    Work.NPC.HasNormalPComplement p G := by
  haveI : Fact p.Prime := ⟨hp⟩
  exact frobenius_npc (hasFrobeniusCondition_of_normalizer_npc h)

end Work.NPC.Frobenius
