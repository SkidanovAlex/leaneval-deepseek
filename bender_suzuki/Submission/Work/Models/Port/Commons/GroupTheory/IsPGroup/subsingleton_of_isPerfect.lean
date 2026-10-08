import Mathlib.GroupTheory.IsPerfect

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Commons.GroupTheory.IsPGroup

theorem subsingleton_of_isPerfect {G : Type*} [Group G] [Finite G] {p : ℕ}
    [Fact (Nat.Prime p)] (hp : IsPGroup p G) (hperf : Group.IsPerfect G) :
    Subsingleton G := by
  by_contra h
  have hnt : Nontrivial G := not_subsingleton_iff_nontrivial.mp h
  have hnil : Group.IsNilpotent G := hp.isNilpotent
  have hperf' : Group.IsPerfect G := hperf
  exact (Group.IsPerfect.not_isSolvable G) inferInstance

end Commons.GroupTheory.IsPGroup