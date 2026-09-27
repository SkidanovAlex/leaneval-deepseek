import Mathlib

namespace Work.EKLComp

theorem sum_prod_mul_log_snd {ι κ : Type*} [Fintype ι] [Fintype κ] (p : ι × κ → ℝ)
    (B : κ → ℝ) :
    ∑ q : ι × κ, p q * Real.log (B q.2) = ∑ j, (∑ i, p (i, j)) * Real.log (B j) := by
  rw [Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  simp only [Finset.sum_mul]

end Work.EKLComp
