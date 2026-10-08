import Mathlib
import Submission.Work.RankOneUniqueness.Basic
import Submission.Work.RankOneUniqueness.canon_exists

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.RankOneUniqueness.gen_top` — `G = ⟨H, t⟩`

The Bruhat decomposition `G = H ∪ H·t·Q` of `canon_exists` shows that `H` and `t` generate
`G`.  This is the form in which the rank-one data determines the whole group, and it is the
`hgen`/`hgen'` hypothesis of `mulEquiv_of_permEquiv`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

open Submission.Blueprint

namespace Work.RankOneUniqueness

theorem gen_top {G : Type} [Group G] {H Q : Subgroup G} {t : G}
    (h : Submission.Blueprint.IsSplitRankOne H Q t) : Subgroup.closure ((H : Set G) ∪ {t}) = ⊤ := by
  refine le_antisymm le_top ?_
  intro g _
  by_cases hmem : g ∈ H
  · exact Subgroup.subset_closure (Or.inl hmem)
  · obtain ⟨a, ha, q, hq, rfl⟩ := canon_exists h hmem
    refine Subgroup.mul_mem _ (Subgroup.mul_mem _ ?_ ?_) ?_
    · exact Subgroup.subset_closure (Or.inl ha)
    · exact Subgroup.subset_closure (Or.inr rfl)
    · exact Subgroup.subset_closure (Or.inl (h.le hq))

end Work.RankOneUniqueness
