import Mathlib

namespace Work.LT

/-- Dirichlet-form identity for the left-averaging walk: the sum of squared edge differences is `2·|ι|·‖f‖²` minus twice the quadratic form. -/
theorem dirichlet_left {G : Type*} [Group G] [Fintype G] {ι : Type*} [Fintype ι]
    (α : ι → G) (f : G → ℝ) :
    (∑ a, ∑ x, (f (α a * x) - f x) ^ 2)
      = 2 * (Fintype.card ι : ℝ) * (∑ x, f x ^ 2) - 2 * ∑ a, ∑ x, f (α a * x) * f x := by
  -- For each `a`, left translation by `α a` permutes `G`, so the squared terms sum to the same value.
  have hsq : ∀ a : ι, (∑ x, f (α a * x) ^ 2) = ∑ x, f x ^ 2 := by
    intro a
    exact Equiv.sum_comp (Equiv.mulLeft (α a)) (fun y => f y ^ 2)
  -- Pointwise expansion of the square, summed over `x`.
  have hterm : ∀ a : ι, (∑ x, (f (α a * x) - f x) ^ 2)
      = 2 * (∑ x, f x ^ 2) - 2 * ∑ x, f (α a * x) * f x := by
    intro a
    have hpoint : ∀ x, (f (α a * x) - f x) ^ 2
        = f (α a * x) ^ 2 - 2 * (f (α a * x) * f x) + f x ^ 2 := by intro x; ring
    rw [Finset.sum_congr rfl (fun x _ => hpoint x)]
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, hsq a]
    ring
  -- Sum the per-`a` identity over `a` and factor out the cardinality.
  rw [Finset.sum_congr rfl (fun a _ => hterm a)]
  rw [Finset.sum_sub_distrib, Finset.sum_const, ← Finset.mul_sum, nsmul_eq_mul, Finset.card_univ]
  ring

end Work.LT
