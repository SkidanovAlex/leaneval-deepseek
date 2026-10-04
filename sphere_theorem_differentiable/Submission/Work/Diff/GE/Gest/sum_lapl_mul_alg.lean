import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.GE.Gest

theorem sum_lapl_mul_alg {ι : Type*} [Fintype ι] (p q : ℝ) (A B C D : ι → ℝ) :
    ∑ i, (p * A i + q * B i + 2 * (C i * D i))
      = p * ∑ i, A i + q * ∑ i, B i + 2 * ∑ i, (C i * D i) := by
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum,
    Finset.mul_sum]

end Work.Diff.GE.Gest
