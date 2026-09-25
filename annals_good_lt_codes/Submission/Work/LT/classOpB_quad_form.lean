import Mathlib
import Submission.Work.LT.lr_local_defs

namespace Work.LT

/-- Reindexing one step of the B-walk: summing `s₁(g)·s₀(g·(B j)⁻¹)` over `g` and letting
`g ↦ g·B j` turns it into `s₀(g)·s₁(g·B j)`. -/
lemma sum_s1_s0_mul_inv_eq {G : Type} [Group G] [Fintype G] {Δ : ℕ} (B : Fin Δ → G)
    (s : Fin 2 × G → ℝ) (j : Fin Δ) :
    (∑ g, s (1, g) * s (0, g * (B j)⁻¹)) = ∑ g, s (0, g) * s (1, g * B j) := by
  rw [← Equiv.sum_comp (Equiv.mulRight (B j)) (fun g => s (1, g) * s (0, g * (B j)⁻¹))]
  apply Finset.sum_congr rfl
  intro h _
  show s (1, h * B j) * s (0, (h * B j) * (B j)⁻¹) = s (0, h) * s (1, h * B j)
  rw [mul_inv_cancel_right, mul_comm]

/-- The quadratic form of the label-`B` walk: `⟨s, classOpB B s⟩ = 2·⟨s₀, classOpB s₁⟩`, where
`s₀ = s(0,·)` and `s₁ = s(1,·)`. Indeed the two "layers" of the sum are equal, by the
reindexing `g ↦ g·B j` of the second layer. -/
lemma classOpB_quad_form {G : Type} [Group G] [Fintype G] {Δ : ℕ} (B : Fin Δ → G)
    (s : Fin 2 × G → ℝ) :
    (∑ p : Fin 2 × G, s p * classOpB B s p)
      = 2 * ∑ g, s (0, g) * ((∑ j, s (1, g * B j)) / (Δ : ℝ)) := by
  -- the odd layer equals the even layer
  have hodd : (∑ g, s (1, g) * ((∑ j, s (0, g * (B j)⁻¹)) / (Δ : ℝ)))
      = ∑ g, s (0, g) * ((∑ j, s (1, g * B j)) / (Δ : ℝ)) := by
    have h1 : ∀ g : G, s (1, g) * ((∑ j, s (0, g * (B j)⁻¹)) / (Δ : ℝ))
        = (∑ j, s (1, g) * s (0, g * (B j)⁻¹)) / (Δ : ℝ) := by
      intro g
      rw [← mul_div_assoc, Finset.mul_sum]
    rw [Finset.sum_congr rfl (fun g _ => h1 g)]
    rw [← Finset.sum_div]
    rw [Finset.sum_comm]
    rw [Finset.sum_congr rfl (fun j _ => sum_s1_s0_mul_inv_eq B s j)]
    rw [Finset.sum_comm]
    rw [Finset.sum_congr rfl
      (fun g _ => (Finset.mul_sum Finset.univ (fun j => s (1, g * B j)) (s (0, g))).symm)]
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro g _
    rw [mul_div_assoc]
  have hsplit : (∑ p : Fin 2 × G, s p * classOpB B s p)
      = (∑ g, s (0, g) * ((∑ j, s (1, g * B j)) / (Δ : ℝ)))
        + ∑ g, s (1, g) * ((∑ j, s (0, g * (B j)⁻¹)) / (Δ : ℝ)) := by
    rw [Fintype.sum_prod_type, Fin.sum_univ_two]
    rw [show (∑ g, s (0, g) * classOpB B s (0, g))
          = ∑ g, s (0, g) * ((∑ j, s (1, g * B j)) / (Δ : ℝ)) from by
        apply Finset.sum_congr rfl; intro g _; simp [classOpB]]
    rw [show (∑ g, s (1, g) * classOpB B s (1, g))
          = ∑ g, s (1, g) * ((∑ j, s (0, g * (B j)⁻¹)) / (Δ : ℝ)) from by
        apply Finset.sum_congr rfl; intro g _; simp [classOpB]]
  rw [hsplit, hodd]
  ring

end Work.LT
