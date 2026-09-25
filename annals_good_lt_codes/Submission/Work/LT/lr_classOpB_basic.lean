import Mathlib
import Submission.Work.LT.lr_local_defs

namespace Work.LT

/-- Basic structural properties of the label-`B` walk operator `classOpB B`: it is `ℝ`-linear,
fixes the constant function `1`, and preserves the total sum (it is a stochastic operator, each
step having probability `1/Δ`). -/
theorem lr_classOpB_basic {G : Type} [Group G] [Fintype G] {Δ : ℕ} (hΔ : 0 < Δ) (B : Fin Δ → G) :
    (∀ x y : Fin 2 × G → ℝ, classOpB B (x + y) = classOpB B x + classOpB B y) ∧
    (∀ (a : ℝ) (x : Fin 2 × G → ℝ), classOpB B (a • x) = a • classOpB B x) ∧
    (classOpB B (fun _ => (1 : ℝ)) = fun _ => (1 : ℝ)) ∧
    (∀ x : Fin 2 × G → ℝ, ∑ p, classOpB B x p = ∑ p, x p) := by
  have hΔne : (Δ : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hΔ)
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- additivity, pointwise
    intro x y
    funext p
    rcases p with ⟨i, g⟩
    fin_cases i <;> simp [classOpB, Finset.sum_add_distrib, add_div]
  · -- homogeneity, pointwise
    intro a x
    funext p
    rcases p with ⟨i, g⟩
    fin_cases i <;> · simp [classOpB]; rw [← Finset.mul_sum, mul_div_assoc]
  · -- the constant function `1` is fixed
    funext p
    rcases p with ⟨i, g⟩
    fin_cases i <;> · simp [classOpB, hΔne]
  · -- the operator preserves the total sum: each layer is reindexed by right multiplication
    intro x
    have h0 : (∑ g, classOpB B x (0, g)) = ∑ g, x (1, g) := by
      have hpt : ∀ g, classOpB B x (0, g) = (∑ j, x (1, g * B j)) / (Δ : ℝ) := by
        intro g; simp [classOpB]
      have hreindex : ∀ j : Fin Δ, (∑ g, x (1, g * B j)) = ∑ g, x (1, g) := fun j =>
        Equiv.sum_comp (Equiv.mulRight (B j)) (fun g => x (1, g))
      rw [Finset.sum_congr rfl (fun g _ => hpt g)]
      rw [← Finset.sum_div]
      rw [Finset.sum_comm]
      rw [Finset.sum_congr rfl (fun j _ => hreindex j)]
      rw [Finset.sum_const, Finset.card_fin, nsmul_eq_mul]
      exact mul_div_cancel_left₀ _ hΔne
    have h1 : (∑ g, classOpB B x (1, g)) = ∑ g, x (0, g) := by
      have hpt : ∀ g, classOpB B x (1, g) = (∑ j, x (0, g * (B j)⁻¹)) / (Δ : ℝ) := by
        intro g; simp [classOpB]
      have hreindex : ∀ j : Fin Δ, (∑ g, x (0, g * (B j)⁻¹)) = ∑ g, x (0, g) := fun j =>
        Equiv.sum_comp (Equiv.mulRight ((B j)⁻¹)) (fun g => x (0, g))
      rw [Finset.sum_congr rfl (fun g _ => hpt g)]
      rw [← Finset.sum_div]
      rw [Finset.sum_comm]
      rw [Finset.sum_congr rfl (fun j _ => hreindex j)]
      rw [Finset.sum_const, Finset.card_fin, nsmul_eq_mul]
      exact mul_div_cancel_left₀ _ hΔne
    have hL : (∑ p : Fin 2 × G, classOpB B x p)
        = (∑ g, classOpB B x (0, g)) + ∑ g, classOpB B x (1, g) := by
      rw [Fintype.sum_prod_type, Fin.sum_univ_two]
    have hR : (∑ p : Fin 2 × G, x p) = (∑ g, x (0, g)) + ∑ g, x (1, g) := by
      rw [Fintype.sum_prod_type, Fin.sum_univ_two]
    rw [hL, hR, h0, h1, add_comm]

end Work.LT
