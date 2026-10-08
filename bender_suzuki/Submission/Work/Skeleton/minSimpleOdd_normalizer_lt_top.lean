import Mathlib
import Submission.Work.Skeleton.Basic

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option linter.style.haveILetI false

namespace Work.Skeleton

/-- If a nontrivial proper subgroup of a minimal counterexample were *normal*, then by
simplicity it would be trivial or the whole group, contradicting the hypotheses; hence its
normalizer is a proper subgroup. -/
theorem minSimpleOdd_normalizer_lt_top {G : Type*} [Group G] [Finite G] (h : MinSimpleOdd G)
    {H : Subgroup G} (hbot : H ≠ ⊥) (htop : H ≠ ⊤) : Subgroup.normalizer (H : Set G) < ⊤ := by
  rw [lt_top_iff_ne_top]
  intro hnorm
  haveI : H.Normal := Subgroup.normalizer_eq_top_iff.mp hnorm
  haveI : IsSimpleGroup G := h.simple
  rcases @IsSimpleGroup.eq_bot_or_eq_top_of_normal _ _ _ H inferInstance with hH | hH
  · exact hbot hH
  · exact htop hH

end Work.Skeleton
