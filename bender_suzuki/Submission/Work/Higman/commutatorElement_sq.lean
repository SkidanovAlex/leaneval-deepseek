import Mathlib

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.Higman

open scoped commutatorElement

/-- The commutator of a square (Mathlib convention `⁅x, y⁆ = x * y * x⁻¹ * y⁻¹`):
`⁅x ^ 2, c⁆ = ⁅x, ⁅x, c⁆⁆ * ⁅x, c⁆ ^ 2`. -/
theorem commutatorElement_sq {G : Type} [Group G] (x c : G) :
    ⁅x ^ 2, c⁆ = ⁅x, ⁅x, c⁆⁆ * ⁅x, c⁆ ^ 2 := by
  -- `⁅x ^ 2, c⁆ = x * ⁅x, c⁆ * x⁻¹ * ⁅x, c⁆` by the left multiplication formula.
  have h1 : ⁅x ^ 2, c⁆ = x * ⁅x, c⁆ * x⁻¹ * ⁅x, c⁆ := by
    rw [pow_two, commutatorElement_mul_left_eq_conj_mul]
  -- And the right-hand side is the same element.
  have h2 : ⁅x, ⁅x, c⁆⁆ * ⁅x, c⁆ ^ 2 = x * ⁅x, c⁆ * x⁻¹ * ⁅x, c⁆ := by
    rw [commutatorElement_def, pow_two]
    group
  rw [h1]
  exact h2.symm

end Work.Higman
