import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.PTW

theorem prod_exp_pow_mult_eq_exp_sum (K : Type) [Field K] [NumberField K]
    (b : NumberField.InfinitePlace K → ℝ) :
    ∏ w : NumberField.InfinitePlace K, Real.exp (b w) ^ w.mult =
      Real.exp (∑ w : NumberField.InfinitePlace K, ((w.mult : ℕ) : ℝ) * b w) := by
  simp_rw [← Real.exp_nat_mul]
  rw [← Real.exp_sum]

end Work.SSGRoute.PTW
