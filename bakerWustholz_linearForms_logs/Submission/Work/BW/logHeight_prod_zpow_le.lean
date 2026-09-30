import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

/-- Subadditivity of `logHeight₁` over a product with integer exponents:
`h(∏ αᵢ^{yᵢ}) ≤ ∑ |yᵢ| · h(αᵢ)`. -/
theorem logHeight_prod_zpow_le {K : Type*} [Field K] [NumberField K] {n : ℕ} (α : Fin n → K)
    (y : Fin n → ℤ) :
    Height.logHeight₁ (∏ i, α i ^ y i) ≤
      ∑ i, ((y i).natAbs : ℝ) * Height.logHeight₁ (α i) := by
  calc Height.logHeight₁ (∏ i, α i ^ y i)
      ≤ ∑ i, Height.logHeight₁ (α i ^ y i) := Height.logHeight₁_prod_le Finset.univ _
    _ = ∑ i, ((y i).natAbs : ℝ) * Height.logHeight₁ (α i) := by
        simp [Height.logHeight₁_zpow]

end Work.BW
