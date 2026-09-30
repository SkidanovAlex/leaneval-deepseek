import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF.mr_direct

theorem cpow_prod_natCast {ι : Type*} (s : Finset ι) (f : ι → ℕ) (w : ℂ) :
    ∏ i ∈ s, ((f i : ℂ) ^ w) = (((∏ i ∈ s, f i : ℕ)) : ℂ) ^ w := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a t ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha, ih, Nat.cast_mul]
    exact (Complex.natCast_mul_natCast_cpow (f a) (∏ i ∈ t, f i) w).symm

end Work.BMF.mr_direct
