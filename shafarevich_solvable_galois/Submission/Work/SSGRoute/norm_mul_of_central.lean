import Mathlib
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute

/-- If `(δ a)⁻¹ * a` is central, then the "norm defect" is multiplicative
up to the order of the factors: the defect of `a * b` equals the product of
the defect of `b` and the defect of `a`. -/
theorem norm_mul_of_central {G : Type*} [Group G] (δ : G →* G) (a b : G)
    (ha : ∀ y : G, ((δ a)⁻¹ * a) * y = y * ((δ a)⁻¹ * a)) :
    (δ (a * b))⁻¹ * (a * b) = ((δ b)⁻¹ * b) * ((δ a)⁻¹ * a) := by
  rw [map_mul, mul_inv_rev]
  rw [mul_assoc ((δ b)⁻¹)]
  rw [← mul_assoc (δ a)⁻¹ a b]
  rw [ha b]
  rw [mul_assoc]

end Work.SSGRoute
