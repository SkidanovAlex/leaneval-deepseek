import Mathlib
import Submission.Work.Fitting.Defs
import Submission.Work.Hall.MinimalNormal.hall_minimalNormal_isElementaryAbelian

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# Minimal normal subgroups of solvable groups are `p`-groups

Let `G` be a finite solvable group and `N ◁ G` a minimal normal subgroup.  Then `N` is a
`p`-group for some prime `p`; in fact `N` is elementary abelian.

The mathematical content is entirely the standard fact (proved in
`Work.Hall.MinimalNormal.hall_minimalNormal_isElementaryAbelian`): a minimal normal subgroup
of a solvable group is abelian of exponent a prime.  We re-export the head of that result in
the vocabulary of `Work.Fitting.IsMinimalNormal` and observe that a group of exponent `p`
with `p` prime is a `p`-group.
-/

namespace Work.Fitting

open Classical

theorem isMinimalNormal_isPGroup (G : Type*) [Group G] [Finite G] [Group.IsSolvable G]
    {N : Subgroup G} (h : Work.Fitting.IsMinimalNormal N) :
    ∃ p : ℕ, p.Prime ∧ IsPGroup p ↥N := by
  obtain ⟨hNnorm, hNne, hNmin⟩ := h
  -- `Work.Fitting.IsMinimalNormal` and `Work.Hall.IsMinimalNormal` differ only in the
  -- orientation of the minimality conclusion, which is the same for `M ≤ N`.
  have hHall : Work.Hall.IsMinimalNormal N :=
    ⟨hNnorm, hNne, fun M hM hle hne => le_of_eq (hNmin M hM hle hne).symm⟩
  -- a subgroup of a solvable group is solvable
  haveI : Group.IsSolvable ↥N := inferInstance
  obtain ⟨p, hp, hEA⟩ :=
    Work.Hall.MinimalNormal.hall_minimalNormal_isElementaryAbelian hHall inferInstance
  refine ⟨p, hp, ?_⟩
  -- `IsElementaryAbelian p N` gives every element of `N` exponent dividing `p`, so `N` is a
  -- `p`-group.
  rw [isPGroup_iff_pow_pow_eq_one]
  intro g
  exact ⟨1, by simpa using (show g ^ p = 1 from hEA.2 g)⟩

end Work.Fitting
