import Mathlib
import Submission.Work.LT.lr_family_defs

namespace Work.LT

/-- Dirichlet form of the lazy 48-letter alphabet `alpha`: for every `x ↦ gᵢ·x` the sum of squared differences appears twice (once for `gᵢ`, once for `gᵢ⁻¹`), while the identities contribute `0`. -/
theorem alpha_dirichlet {G : Type*} [Group G] [Fintype G] (g : Fin 12 → G) (f : G → ℝ) :
    (∑ a : Fin 12 × Bool × Bool, ∑ x, (f (_root_.Work.LT.RF.alpha g a * x) - f x) ^ 2)
      = 2 * ∑ i : Fin 12, ∑ x, (f (g i * x) - f x) ^ 2 := by
  -- Left translation by `h` and by `h⁻¹` give the same sum of squared differences.
  have hsymm : ∀ h : G, (∑ x, (f (h⁻¹ * x) - f x) ^ 2) = ∑ x, (f (h * x) - f x) ^ 2 := by
    intro h
    have h1 : (∑ x, (f (h⁻¹ * x) - f x) ^ 2) = ∑ x, (f x - f (h * x)) ^ 2 := by
      rw [← Equiv.sum_comp (Equiv.mulLeft h) (fun y => (f (h⁻¹ * y) - f y) ^ 2)]
      apply Finset.sum_congr rfl
      intro x _
      show (f (h⁻¹ * (h * x)) - f (h * x)) ^ 2 = (f x - f (h * x)) ^ 2
      rw [inv_mul_cancel_left]
    rw [h1]
    apply Finset.sum_congr rfl
    intro x _
    ring
  -- Split the alphabet index set `Fin 12 × Bool × Bool` into its four `Bool`-cases per generator.
  calc (∑ a : Fin 12 × Bool × Bool, ∑ x, (f (_root_.Work.LT.RF.alpha g a * x) - f x) ^ 2)
      = ∑ i : Fin 12, 2 * ∑ x, (f (g i * x) - f x) ^ 2 := by
        rw [Fintype.sum_prod_type]
        apply Finset.sum_congr rfl
        intro i _
        rw [Fintype.sum_prod_type, Fintype.sum_bool, Fintype.sum_bool, Fintype.sum_bool]
        have e1 : _root_.Work.LT.RF.alpha g (i, (true, true)) = g i := by
          simp [_root_.Work.LT.RF.alpha]
        have e2 : _root_.Work.LT.RF.alpha g (i, (true, false)) = (g i)⁻¹ := by
          simp [_root_.Work.LT.RF.alpha]
        have e3 : _root_.Work.LT.RF.alpha g (i, (false, true)) = 1 := by
          simp [_root_.Work.LT.RF.alpha]
        have e4 : _root_.Work.LT.RF.alpha g (i, (false, false)) = 1 := by
          simp [_root_.Work.LT.RF.alpha]
        have hz1 : (∑ x, (f (_root_.Work.LT.RF.alpha g (i, (false, true)) * x) - f x) ^ 2) = 0 := by
          rw [e3]; simp
        have hz2 : (∑ x, (f (_root_.Work.LT.RF.alpha g (i, (false, false)) * x) - f x) ^ 2) = 0 := by
          rw [e4]; simp
        rw [e1, e2, hz1, hz2, hsymm (g i)]
        ring
    _ = 2 * ∑ i : Fin 12, ∑ x, (f (g i * x) - f x) ^ 2 := by
        rw [Finset.mul_sum]

end Work.LT
