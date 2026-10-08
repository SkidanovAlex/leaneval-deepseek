import Mathlib
import Submission.Work.Skeleton.Basic
import Submission.Work.Skeleton.minSimpleOdd_not_isCoatom_bot

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option linter.style.haveILetI false

namespace Work.Skeleton

/-- **Maximal subgroups of a minimal counterexample are self-normalizing.**

Let `M` be a maximal subgroup (a coatom of the subgroup lattice) of a minimal
counterexample `G` to the odd order theorem.  If `N_G(M) ≠ M`, then `M < N_G(M)`
because `M ≤ N_G(M)` always; maximality of `M` forces `N_G(M) = ⊤`, i.e. `M` is normal
in `G`.  By simplicity `M` is then either `⊥` or `⊤`: it is not `⊤` because it is a
coatom, and it is not `⊥` because `⊥` is not a coatom of a minimal counterexample
(`Work.Skeleton.minSimpleOdd_not_isCoatom_bot`). -/
theorem minSimpleOdd_normalizer_eq_self_of_isCoatom {G : Type*} [Group G] [Finite G]
    (h : MinSimpleOdd G) {M : Subgroup G} (hM : IsCoatom M) :
    Subgroup.normalizer (M : Set G) = M := by
  haveI : IsSimpleGroup G := h.simple
  by_contra hne
  -- `M ≤ N_G(M)`, and by assumption they differ, so `M < N_G(M)`.
  have hlt : M < Subgroup.normalizer (M : Set G) :=
    lt_of_le_of_ne Subgroup.le_normalizer (Ne.symm hne)
  -- Maximality of `M` then forces `N_G(M) = ⊤`.
  have htop : Subgroup.normalizer (M : Set G) = ⊤ := hM.lt_iff.mp hlt
  -- Hence `M` is normal in `G`.
  haveI : M.Normal := Subgroup.normalizer_eq_top_iff.mp htop
  -- By simplicity `M = ⊥` or `M = ⊤`, both impossible for a coatom.
  rcases @IsSimpleGroup.eq_bot_or_eq_top_of_normal _ _ _ M inferInstance with hMbot | hMtop
  · exact minSimpleOdd_not_isCoatom_bot h (hMbot ▸ hM)
  · exact hM.ne_top hMtop

end Work.Skeleton
