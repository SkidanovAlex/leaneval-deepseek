/-
Area A9 (normal `p`-complement theorems): **a group whose Sylow `p`-subgroup is conjugacy-closed has
a normal `p`-complement** — the (1) ⟹ (2) direction of Frobenius' normal `p`-complement theorem.

The proof is in `npc_of_conjugacyClosed_sylow` (a direct argument: the `p`-residual `O^p(G)` meets
`P` trivially and `G ⧸ O^p(G)` is a `p`-group, so the transfer engine
`Work.NPC.hasNormalPComplement_of_hom_to_pGroup` applies); this file only re-exports it under the
name used in the blueprint.  (It does not use the transfer criterion `P* = ⁅P,P⁆`.)
-/
import Mathlib
import Submission.Work.NPC.Defs
import Submission.Work.NPC.Engine
import Submission.Work.NPC.Frobenius.npc_of_conjugacyClosed_sylow

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.NPC.Frobenius

theorem hasNormalPComplement_of_conjugacyClosed_sylow {G : Type*} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime] (P : Sylow p G)
    (h : ∀ x y : ↥(P : Subgroup G), IsConj (x : G) (y : G) → IsConj x y) :
    Work.NPC.HasNormalPComplement p G :=
  npc_of_conjugacyClosed_sylow P h

end Work.NPC.Frobenius
