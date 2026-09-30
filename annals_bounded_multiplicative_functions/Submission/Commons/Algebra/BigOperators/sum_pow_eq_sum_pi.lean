import Mathlib.Algebra.BigOperators.Ring.Finset

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Commons.Algebra.BigOperators

theorem sum_pow_eq_sum_pi {α R : Type*} [Fintype α] [CommSemiring R] (f : α → R) (n : ℕ) :
    (∑ i : α, f i) ^ n = ∑ u : Fin n → α, ∏ r : Fin n, f (u r) := by
  exact Fintype.sum_pow f n

end Commons.Algebra.BigOperators