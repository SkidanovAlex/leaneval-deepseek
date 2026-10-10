import Mathlib

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.PointlessIndexFive

/-- **The orbit-divisor computation.**  Let `σ` be an endomorphism of an additive commutative
group `A` and put `N(y) = y + σ y + σ² y + σ³ y + σ⁴ y`.  For every `y` with `N(y) = 0`, the
`5`-fold multiple `5 • y` is a `(σ - 1)`-boundary: indeed
`5y - N(y) = Σ_{i<5} (y - σ^i y) = Σ_{i<5} (σ - 1)(-(y + σy + … + σ^{i-1}y))`, i.e. each
`y - σ^i y` is minus the shift of a partial sum.  Equivalently the group `ker N / (σ - 1)A` has
exponent dividing `5`. -/
theorem five_nsmul_mem_shift_range {A : Type*} [AddCommGroup A] (σ : A →+ A) (y : A)
    (hy : y + σ y + σ (σ y) + σ (σ (σ y)) + σ (σ (σ (σ y))) = 0) :
    ∃ z : A, σ z - z = (5 : ℕ) • y := by
  -- `z = -(4y + 3σy + 2σ²y + σ³y)` is minus the sum of the partial sums
  -- `Σ_{i<5} Σ_{j<i} σ^j y`; it works because `5y = Σ_{i<5}(y - σ^i y)`.
  refine ⟨-(4 • y + 3 • σ y + 2 • σ (σ y) + σ (σ (σ y))), ?_⟩
  simp only [map_neg, map_add, map_nsmul]
  have he : σ (σ (σ (σ y))) = -(y + σ y + σ (σ y) + σ (σ (σ y))) :=
    eq_neg_of_add_eq_zero_right hy
  rw [he]
  abel

end Work.PointlessIndexFive
