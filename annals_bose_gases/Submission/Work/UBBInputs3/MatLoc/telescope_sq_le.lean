import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Order.Star.Real
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.UBBInputs3.MatLoc

/-- Telescoping + Cauchy–Schwarz: the squared total increment is bounded by `m` times the
sum of the squared increments along the `m` steps. -/
theorem telescope_sq_le (f : ℤ → ℝ) (m : ℕ) (s : ℤ) :
    (f (s + (m : ℤ)) - f s) ^ 2
      ≤ (m : ℝ) * ∑ i ∈ Finset.range m, (f (s + (i : ℤ) + 1) - f (s + (i : ℤ))) ^ 2 := by
  have key : ∑ i ∈ Finset.range m, (f (s + (i : ℤ) + 1) - f (s + (i : ℤ)))
      = f (s + (m : ℤ)) - f s := by
    have h := Finset.sum_range_sub (fun i : ℕ => f (s + (i : ℤ))) m
    simp only [Nat.cast_zero, add_zero] at h
    rw [← h]
    apply Finset.sum_congr rfl
    intro i _
    push_cast
    ring_nf
  rw [← key]
  simpa using sq_sum_le_card_mul_sum_sq (s := Finset.range m)
    (f := fun i => f (s + (i : ℤ) + 1) - f (s + (i : ℤ)))

end Work.UBBInputs3.MatLoc
