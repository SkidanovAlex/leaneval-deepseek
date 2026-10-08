import Mathlib
import Submission.Work.NPC.All
import Submission.Work.ThompsonFrobenius.subgroupOfMulEquivInf

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# Heredity of `HasNormalPComplement` to `N_L(Q)` (area `ThompsonFrobenius`)

If the normalizer `N_G(Q)` of a subgroup `Q` has a normal `p`-complement, then so does the
normalizer `N_L(Q)` computed inside any subgroup `L ≥ Q`: `N_L(Q) ≅ N_G(Q) ⊓ L ≤ N_G(Q)` and
`HasNormalPComplement` is inherited by subgroups (`Work.NPC.Basic.hasNormalPComplement_mono`).

This is the transport used in step GT-c of Theorem D (`npc_of_le`), where the hypothesis of the
induction hypothesis is about `N_L(Z(J(P|_L))) = N_L(Z(J(P)))` and the global hypothesis
`h.hyp` is about `N_G(Z(J(P)))`.
-/

set_option autoImplicit false

namespace Work.ThompsonFrobenius

theorem hasNormalPComplement_normalizer_subgroupOf {G : Type} [Group G] [Finite G] {p : ℕ}
    {A L : Subgroup G} (hAL : A ≤ L)
    (h : Work.NPC.HasNormalPComplement p ↥(Subgroup.normalizer (A : Set G))) :
    Work.NPC.HasNormalPComplement p ↥(Subgroup.normalizer (A.subgroupOf L : Set ↥L)) := by
  rw [← Subgroup.subgroupOf_normalizer_eq hAL]
  have hM : Work.NPC.HasNormalPComplement p
      ↥((Subgroup.normalizer (A : Set G) ⊓ L).subgroupOf
        (Subgroup.normalizer (A : Set G))) :=
    Work.NPC.Basic.hasNormalPComplement_mono _ h
  exact Work.NPC.Basic.hasNormalPComplement_congr
    (normalizerSubgroupOfEquiv (Subgroup.normalizer (A : Set G)) L) hM

end Work.ThompsonFrobenius
