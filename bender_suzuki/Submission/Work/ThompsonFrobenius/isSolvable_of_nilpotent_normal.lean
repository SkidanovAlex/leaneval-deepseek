import Mathlib

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# M3: nilpotent-by-nilpotent is solvable (area `ThompsonFrobenius`)

A subgroup `N ⊴ K` with `N` and `K ⧸ N` nilpotent, hence solvable, has `K` solvable by
Mathlib's `Group.isSolvable_of_subgroup_quotient`.
-/

set_option autoImplicit false

namespace Work.ThompsonFrobenius

theorem isSolvable_of_nilpotent_normal {K : Type*} [Group K] (N : Subgroup K) [N.Normal]
    (hN : Group.IsNilpotent ↥N) (hQ : Group.IsNilpotent (K ⧸ N)) : Group.IsSolvable K := by
  haveI := hN
  haveI := hQ
  exact Group.isSolvable_of_subgroup_quotient N

end Work.ThompsonFrobenius
