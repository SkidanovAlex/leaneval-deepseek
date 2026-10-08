import Mathlib.GroupTheory.OrderOfElement

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Commons.GroupTheory.Subgroup

theorem mem_of_sq_eq_one_of_odd_index {G : Type*} [Group G] (N : Subgroup G) [N.Normal]
    (hodd : Odd N.index) {x : G} (hx : x * x = 1) : x ∈ N := by
  rw [← QuotientGroup.ker_mk' N, MonoidHom.mem_ker]
  set y := QuotientGroup.mk' N x with hy
  have hy2 : y ^ 2 = 1 := by
    rw [pow_two, hy, ← map_mul, hx, map_one]
  have hdvd2 : orderOf y ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr hy2
  have hdvd_index : orderOf y ∣ N.index := by
    rw [Subgroup.index_eq_card]
    exact orderOf_dvd_natCard y
  have hgcd : Nat.gcd 2 N.index = 1 := hodd.coprime_two_left.gcd_eq_one
  have hone : orderOf y ∣ 1 := by
    rw [← hgcd]
    exact Nat.dvd_gcd hdvd2 hdvd_index
  exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp hone)

end Commons.GroupTheory.Subgroup