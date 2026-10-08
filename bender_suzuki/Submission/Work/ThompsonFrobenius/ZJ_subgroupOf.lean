import Mathlib
import Submission.Work.ThompsonFrobenius.BlueprintZJ
import Submission.Work.ThompsonFrobenius.ZJ_map_of_ker_inf_eq_bot
import Submission.Work.ThompsonFrobenius.ZJ_le

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Z(J(P))` inside an intermediate subgroup (area `ThompsonFrobenius`)

Z5 of `NOTES_LEAD_bs_thompson.md`: for `P ≤ K`, the `ZJ` of `P` computed inside the subgroup
«`K` is the `ZJ` of `P` intersected with `K`.

The proof is the transport statement `ZJ_map_of_ker_inf_eq_bot` applied to the injection
`K.subtype : K →* G`: `map K.subtype` is injective on subgroups, and
`(A.subgroupOf K).map K.subtype = A ⊓ K` for any `A ≤ G`.
-/

set_option autoImplicit false

namespace Work.ThompsonFrobenius

theorem ZJ_subgroupOf {G : Type*} [Group G] [Finite G] {P K : Subgroup G} (hPK : P ≤ K) :
    Submission.Blueprint.ZJ (P.subgroupOf K) = (Submission.Blueprint.ZJ P).subgroupOf K := by
  refine Subgroup.map_injective K.subtype_injective ?_
  have hker : K.subtype.ker ⊓ P.subgroupOf K = ⊥ := by
    rw [Subgroup.ker_subtype, bot_inf_eq]
  rw [ZJ_map_of_ker_inf_eq_bot K.subtype (P.subgroupOf K) hker,
    Subgroup.subgroupOf_map_subtype, Subgroup.subgroupOf_map_subtype,
    inf_eq_left.mpr hPK]
  exact (inf_eq_left.mpr (le_trans (ZJ_le P) hPK)).symm

end Work.ThompsonFrobenius
