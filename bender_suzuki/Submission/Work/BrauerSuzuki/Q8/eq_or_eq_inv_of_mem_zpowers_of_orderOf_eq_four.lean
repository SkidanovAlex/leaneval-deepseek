import Mathlib

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.BrauerSuzuki.Q8

theorem eq_or_eq_inv_of_mem_zpowers_of_orderOf_eq_four {G : Type*} [Group G] {x y : G}
    (hx4 : orderOf x = 4) (hy : y ∈ Subgroup.zpowers x) (hy4 : orderOf y = 4) :
    y = x ∨ y = x⁻¹ := by
  classical
  -- `x` has finite order, so `y ∈ ⟨x⟩` means `y = x ^ k` for some `k < orderOf x = 4`.
  have hxfin : IsOfFinOrder x := by
    rw [← orderOf_pos_iff, hx4]; norm_num
  rw [hxfin.mem_zpowers_iff_mem_range_orderOf, Finset.mem_image] at hy
  obtain ⟨k, hk, hky⟩ := hy
  rw [Finset.mem_range, hx4] at hk
  subst y
  -- Now `y = x ^ k` with `k < 4`, so `k ∈ {0,1,2,3}`.
  interval_cases k
  · -- `k = 0`: `y = 1` has order `1 ≠ 4`.
    rw [pow_zero, orderOf_one] at hy4
    omega
  · -- `k = 1`: `y = x`.
    left; rw [pow_one]
  · -- `k = 2`: `y = x ^ 2` has order dividing `2`, so at most `2 ≠ 4`.
    exfalso
    have hdvd : orderOf (x ^ 2) ∣ 2 := by
      apply orderOf_dvd_of_pow_eq_one
      rw [← pow_mul]
      norm_num
      rw [← hx4, pow_orderOf_eq_one]
    have hle : orderOf (x ^ 2) ≤ 2 := Nat.le_of_dvd (by norm_num) hdvd
    omega
  · -- `k = 3`: `y = x ^ 3 = x⁻¹` since `x ^ 4 = 1`.
    right
    have h : x ^ 3 * x = 1 := by
      rw [← pow_succ]
      norm_num
      rw [← hx4, pow_orderOf_eq_one]
    exact eq_inv_of_mul_eq_one_left h

end Work.BrauerSuzuki.Q8
