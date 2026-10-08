import Mathlib

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.ThmF.ChV3.Prove

/-- If `y ^ 2 ∈ H` and `y` has odd order, then `y ∈ H`.

Since `orderOf y = 2 * k + 1` is odd, `y ^ (2 * k) * y = y ^ (2 * k + 1) = 1`,
so `y = (y ^ (2 * k))⁻¹ = ((y ^ 2) ^ k)⁻¹`, an inverse of a power of `y ^ 2 ∈ H`,
hence itself in `H`. -/
theorem mem_of_sq_mem_of_odd_orderOf {G : Type} [Group G] {H : Subgroup G} {y : G}
    (hy : y ^ 2 ∈ H) (hodd : Odd (orderOf y)) : y ∈ H := by
  obtain ⟨k, hk⟩ := hodd
  have hpow : y ^ (2 * k + 1) = 1 := by
    rw [← hk]; exact pow_orderOf_eq_one y
  have h1 : y ^ (2 * k) * y = 1 := by
    rw [← pow_succ]; exact hpow
  have h2 : y = (y ^ (2 * k))⁻¹ := eq_inv_of_mul_eq_one_right h1
  rw [pow_mul] at h2
  rw [h2]
  exact H.inv_mem (H.pow_mem hy k)

end Work.ThmF.ChV3.Prove
