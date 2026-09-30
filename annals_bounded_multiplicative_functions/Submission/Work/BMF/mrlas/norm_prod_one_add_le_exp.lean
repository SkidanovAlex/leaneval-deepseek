import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF.mrlas

/-- The norm of a finite product of factors `1 + h n` is at most the exponential of the
sum of the norms `‖h n‖`.  This is the standard bound obtained from
`‖1 + h n‖ ≤ 1 + ‖h n‖ ≤ exp ‖h n‖` together with the multiplicativity of the norm. -/
theorem norm_prod_one_add_le_exp {ι : Type*} (S : Finset ι) (h : ι → ℂ) :
    ‖∏ n ∈ S, (1 + h n)‖ ≤ Real.exp (∑ n ∈ S, ‖h n‖) := by
  calc ‖∏ n ∈ S, (1 + h n)‖ ≤ ∏ n ∈ S, ‖1 + h n‖ := Finset.norm_prod_le S _
    _ ≤ ∏ n ∈ S, (1 + ‖h n‖) := by
        apply Finset.prod_le_prod₀ (fun n _ => norm_nonneg _)
        intro n _
        simpa using norm_add_le (1 : ℂ) (h n)
    _ ≤ Real.exp (∑ n ∈ S, ‖h n‖) := Real.prod_one_add_le_exp_sum S (fun n => norm_nonneg _)

end Work.BMF.mrlas
