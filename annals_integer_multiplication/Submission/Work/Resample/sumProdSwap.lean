import Mathlib

namespace Work.Resample

/-- Swap the outer sum over `α` with the inner sum over `β` in a product of two
finite products, moving the weights `u y` outside. -/
theorem sumProdSwap {α β : Type*} [Fintype α] [Fintype β] (n : ℕ)
    (A : ℕ → α → ℂ) (B : ℕ → α → β → ℂ) (u : β → ℂ) :
    (∑ x : α, (∏ i ∈ Finset.range n, A i x) * (∑ y : β, (∏ i ∈ Finset.range n, B i x y) * u y))
      = ∑ y : β, (∑ x : α, ∏ i ∈ Finset.range n, A i x * B i x y) * u y := by
  simp only [Finset.mul_sum, Finset.sum_mul, Finset.prod_mul_distrib]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun y _ => Finset.sum_congr rfl (fun x _ => ?_))
  ring

end Work.Resample
