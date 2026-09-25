import Mathlib
import Submission.Work.LT.lr_family_defs

namespace Work.LT

open Finset

/-- Reindexing the sum by left translation: summing `x ↦ f (h⁻¹ * x) * f x` gives the same as
summing `x ↦ f (h * x) * f x`, because `x ↦ h * x` is a bijection of `G` and multiplication
in `ℝ` is commutative. -/
lemma alpha_inv_sum {G : Type*} [Group G] [Fintype G] (h : G) (f : G → ℝ) :
    (∑ x : G, f (h⁻¹ * x) * f x) = ∑ x : G, f (h * x) * f x := by
  rw [← Equiv.sum_comp (Equiv.mulLeft h) (fun x => f (h⁻¹ * x) * f x)]
  simp only [Equiv.coe_mulLeft, inv_mul_cancel_left]
  exact Finset.sum_congr rfl fun x _ => by rw [mul_comm]

/-- The contribution of the four pairs `(b₁, b₂)` of the alphabet for a fixed generator index `i`:
the two identity letters contribute `2‖f‖²` and the two letters `g i`, `(g i)⁻¹` contribute
`2 ∑ x, f (g i * x) * f x`. -/
lemma alpha_quad_inner {G : Type*} [Group G] [Fintype G] (g : Fin 12 → G) (f : G → ℝ)
    (i : Fin 12) :
    (∑ b1 : Bool, ∑ b2 : Bool, ∑ x : G, f (_root_.Work.LT.RF.alpha g (i, b1, b2) * x) * f x)
      = 2 * (∑ x, f (g i * x) * f x) + 2 * _root_.Work.LT.RF.l2 f := by
  rw [Fintype.sum_bool]
  simp only [Fintype.sum_bool, _root_.Work.LT.RF.alpha, Bool.false_eq_true, ite_true, ite_false,
    one_mul]
  rw [alpha_inv_sum (g i) f]
  simp only [_root_.Work.LT.RF.l2, pow_two]
  ring

/-- Quadratic form of the lazy 48-letter alphabet `alpha`: twice the quadratic form of the 12 generators plus `24‖f‖²` from the `24` identity letters. -/
theorem alpha_quad {G : Type*} [Group G] [Fintype G] (g : Fin 12 → G) (f : G → ℝ) :
    (∑ a : Fin 12 × Bool × Bool, ∑ x, f (_root_.Work.LT.RF.alpha g a * x) * f x)
      = 2 * (∑ i : Fin 12, ∑ x, f (g i * x) * f x) + 24 * _root_.Work.LT.RF.l2 f := by
  have hsplit : (∑ a : Fin 12 × Bool × Bool, ∑ x, f (_root_.Work.LT.RF.alpha g a * x) * f x)
      = ∑ i : Fin 12,
          (∑ b1 : Bool, ∑ b2 : Bool,
            ∑ x, f (_root_.Work.LT.RF.alpha g (i, b1, b2) * x) * f x) := by
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Fintype.sum_prod_type]
  rw [hsplit, Finset.sum_congr rfl fun i _ => alpha_quad_inner g f i]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum]
  congr 1
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

end Work.LT
