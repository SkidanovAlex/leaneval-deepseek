import Mathlib
import Submission.Work.Fitting.Defs

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.Fitting

/-- A minimal normal subgroup `N` of an arbitrary group `G` which is not abelian is
perfect: `⁅N, N⁆ = N`.

Indeed `⁅N, N⁆` is a normal subgroup of `G` (the commutator of two normal subgroups),
it is contained in `N`, and it is nontrivial precisely when `N` is nonabelian.
Minimality of `N` then forces `⁅N, N⁆ = N`. -/
theorem isMinimalNormal_commutator_eq_self {G : Type*} [Group G] {N : Subgroup G}
    (h : Work.Fitting.IsMinimalNormal N) (hne : ¬ IsMulCommutative ↥N) : ⁅N, N⁆ = N := by
  obtain ⟨hnorm, _hbot, hmin⟩ := h
  haveI := hnorm
  refine hmin ⁅N, N⁆ inferInstance (Subgroup.commutator_le_left N N) ?_
  intro hcon
  exact hne ((Subgroup.commutator_self_eq_bot_iff (H := N)).mp hcon)

end Work.Fitting
