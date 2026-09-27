import Mathlib

namespace Work.EKLComp

theorem sum_prod_mul_log_fst {ι κ : Type*} [Fintype ι] [Fintype κ] (p : ι × κ → ℝ)
    (A : ι → ℝ) :
    ∑ q : ι × κ, p q * Real.log (A q.1) = ∑ i, (∑ j, p (i, j)) * Real.log (A i) := by
  rw [Fintype.sum_prod_type]
  congr 1 with i
  rw [Finset.sum_mul]

end Work.EKLComp
