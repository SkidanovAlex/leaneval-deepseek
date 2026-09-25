import Mathlib

namespace Work.LT

/-- The left-averaging quadratic form `(u,v) ↦ ∑_a ∑_x u (α_a · x) v x` is symmetric when the list `α` is closed under inversion through the permutation `η`. -/
theorem quad_symm_left {G : Type*} [Group G] [Fintype G] {ι : Type*} [Fintype ι]
    (α : ι → G) (η : ι ≃ ι) (hη : ∀ a, α (η a) = (α a)⁻¹) (u v : G → ℝ) :
    (∑ a, ∑ x, u (α a * x) * v x) = ∑ a, ∑ x, v (α a * x) * u x := by
  calc ∑ a, ∑ x, u (α a * x) * v x
      = ∑ a, ∑ x, u ((α a)⁻¹ * x) * v x := by
        rw [← Equiv.sum_comp η (fun a => ∑ x, u (α a * x) * v x)]
        exact Finset.sum_congr rfl (fun a _ => by rw [hη])
    _ = ∑ a, ∑ x, v (α a * x) * u x := by
        apply Finset.sum_congr rfl
        intro a _
        rw [← Equiv.sum_comp (Equiv.mulLeft (α a)) (fun x => u ((α a)⁻¹ * x) * v x)]
        apply Finset.sum_congr rfl
        intro x _
        simp [Equiv.mulLeft, Units.mulLeft_apply, inv_mul_cancel_left, mul_comm]

end Work.LT
