import Mathlib
import Submission.Work.LT.lr_local_defs

set_option linter.unusedSectionVars false

namespace Work.LT

open Classical
open scoped BigOperators

variable {G : Type*} [Group G] [Fintype G] {Δ : ℕ}

/-- `a * ((∑ j, X j) / c) = (∑ j, a * X j) / c`. -/
lemma mul_sum_div {Δ : ℕ} (a : ℝ) (X : Fin Δ → ℝ) (c : ℝ) :
    a * ((∑ j, X j) / c) = (∑ j, a * X j) / c := by
  rw [← mul_div_assoc, Finset.mul_sum]

/-- Pull a constant divisor out of a double sum. -/
lemma sum_sum_div {G : Type*} [Fintype G] {Δ : ℕ} (F : G → Fin Δ → ℝ) (c : ℝ) :
    (∑ g : G, (∑ j : Fin Δ, F g j) / c) = (∑ g : G, ∑ j : Fin Δ, F g j) / c := by
  rw [← Finset.sum_div]

/-- Reindexing identity for the right-regular B-step walk: summing `f₁` against the `(B j)⁻¹`-shift
of `f₀` is the same as summing `f₀` against the `B j`-shift of `f₁`. -/
lemma sum_mul_inv_eq (B : Fin Δ → G) (f₀ f₁ : G → ℝ) :
    (∑ g : G, ∑ j : Fin Δ, f₁ g * f₀ (g * (B j)⁻¹))
      = ∑ g : G, ∑ j : Fin Δ, f₀ g * f₁ (g * B j) := by
  have key : ∀ j : Fin Δ, (∑ g : G, f₁ g * f₀ (g * (B j)⁻¹)) = ∑ g : G, f₀ g * f₁ (g * B j) := by
    intro j
    rw [← Equiv.sum_comp (Equiv.mulRight (B j)) (fun g => f₁ g * f₀ (g * (B j)⁻¹))]
    apply Finset.sum_congr rfl
    intro g _
    simp only [Equiv.coe_mulRight]
    rw [mul_inv_cancel_right]
    ring
  calc (∑ g : G, ∑ j : Fin Δ, f₁ g * f₀ (g * (B j)⁻¹))
      = ∑ j : Fin Δ, ∑ g : G, f₁ g * f₀ (g * (B j)⁻¹) := Finset.sum_comm
    _ = ∑ j : Fin Δ, ∑ g : G, f₀ g * f₁ (g * B j) := by
          apply Finset.sum_congr rfl; intro j _; exact key j
    _ = ∑ g : G, ∑ j : Fin Δ, f₀ g * f₁ (g * B j) := Finset.sum_comm

/-- Expansion of the vertex sum over `(α,β,g)` into the `β = 0` and `β = 1` parts. -/
lemma lr_MB_expand (B : Fin Δ → G) (h : Vtx G → ℝ) :
    (∑ v : Vtx G, h v * ((∑ j : Fin Δ, h (nB B v j)) / (Δ : ℝ)))
      = (∑ α : Fin 2, ∑ g : G, h (α,0,g) * ((∑ j : Fin Δ, h (α,1,g * B j)) / (Δ : ℝ)))
        + (∑ α : Fin 2, ∑ g : G, h (α,1,g) * ((∑ j : Fin Δ, h (α,0,g * (B j)⁻¹)) / (Δ : ℝ))) := by
  rw [Fintype.sum_prod_type]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro α _
  rw [Fintype.sum_prod_type, Fin.sum_univ_two]
  simp only [nB, Fin.isValue, Fin.reduceEq, ite_true, ite_false]

/-- The `β = 1` part of the expansion equals the `β = 0` part. -/
lemma lr_MB_beta_eq (B : Fin Δ → G) (h : Vtx G → ℝ) :
    (∑ α : Fin 2, ∑ g : G, h (α,1,g) * ((∑ j : Fin Δ, h (α,0,g * (B j)⁻¹)) / (Δ : ℝ)))
      = ∑ α : Fin 2, ∑ g : G, h (α,0,g) * ((∑ j : Fin Δ, h (α,1,g * B j)) / (Δ : ℝ)) := by
  apply Finset.sum_congr rfl
  intro α _
  rw [show (∑ g : G, h (α,1,g) * ((∑ j : Fin Δ, h (α,0,g * (B j)⁻¹)) / (Δ:ℝ)))
        = ∑ g : G, ((∑ j : Fin Δ, h (α,1,g) * h (α,0, g * (B j)⁻¹)) / (Δ:ℝ)) from by
      apply Finset.sum_congr rfl; intro g _
      exact mul_sum_div (h (α,1,g)) (fun j => h (α,0, g*(B j)⁻¹)) (Δ:ℝ)]
  rw [sum_sum_div (fun g j => h (α,1,g) * h (α,0, g*(B j)⁻¹)) (Δ:ℝ)]
  rw [show (∑ g : G, h (α,0,g) * ((∑ j : Fin Δ, h (α,1,g * B j)) / (Δ:ℝ)))
        = ∑ g : G, ((∑ j : Fin Δ, h (α,0,g) * h (α,1, g * B j)) / (Δ:ℝ)) from by
      apply Finset.sum_congr rfl; intro g _
      exact mul_sum_div (h (α,0,g)) (fun j => h (α,1, g*B j)) (Δ:ℝ)]
  rw [sum_sum_div (fun g j => h (α,0,g) * h (α,1, g*B j)) (Δ:ℝ)]
  rw [sum_mul_inv_eq B (fun g => h (α,0,g)) (fun g => h (α,1,g))]

theorem lr_MB_form {G : Type} [Group G] [Fintype G] {Δ : ℕ} (B : Fin Δ → G) (h : Vtx G → ℝ) :
    (∑ v : Vtx G, h v * ((∑ j : Fin Δ, h (nB B v j)) / (Δ : ℝ)))
      = 2 * ∑ α : Fin 2, ∑ g : G,
          h (α, 0, g) * ((∑ j : Fin Δ, h (α, 1, g * B j)) / (Δ : ℝ)) := by
  rw [lr_MB_expand B h, lr_MB_beta_eq B h]
  ring

end Work.LT
