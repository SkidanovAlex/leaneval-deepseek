import Mathlib
import Submission.Work.BW.mvdefs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

open Finset

/-- Pointwise expansion of `2 * (∑_j ε_j cos (c θ_j))^2` as a double sum, using the product
to sum identity `2 cos a cos b = cos (a+b) + cos (a-b)`. -/
lemma two_mul_sq_sum {n : ℕ} (ε θ : Fin n → ℝ) (c : ℝ) :
    2 * (∑ j, ε j * Real.cos (c * θ j))^2
      = ∑ j, ∑ l, ε j * ε l * (Real.cos (c*(θ j + θ l)) + Real.cos (c*(θ j - θ l))) := by
  rw [sq, Finset.sum_mul_sum]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl; intro j _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl; intro l _
  rw [show c * (θ j + θ l) = c*θ j + c*θ l by ring,
      show c * (θ j - θ l) = c*θ j - c*θ l by ring,
      Real.cos_add, Real.cos_sub]
  ring

/-- The exact expansion of twice the Fejér-weighted second moment:
`2 ∑_k w_k (∑_j ε_j cos (2π k θ_j))^2 = ∑_{j,l} ε_j ε_l (T_K(θ_j+θ_l) + T_K(θ_j-θ_l))`. -/
lemma fejer_expand {n : ℕ} (ε θ : Fin n → ℝ) (K : ℕ) :
    2 * (∑ k ∈ Finset.Icc 1 K, fejerW K k * (∑ j, ε j * Real.cos (2*Real.pi*k*θ j))^2)
      = ∑ j, ∑ l, ε j * ε l * (fejerT K (θ j + θ l) + fejerT K (θ j - θ l)) := by
  rw [Finset.mul_sum]
  have hstep : ∀ k ∈ Finset.Icc 1 K,
      2 * (fejerW K k * (∑ j, ε j * Real.cos (2*Real.pi*k*θ j))^2)
      = ∑ j, ∑ l, fejerW K k * (ε j * ε l *
          (Real.cos (2*Real.pi*k*(θ j + θ l)) + Real.cos (2*Real.pi*k*(θ j - θ l)))) := by
    intro k _
    rw [show (2:ℝ) * (fejerW K k * (∑ j, ε j * Real.cos (2*Real.pi*k*θ j))^2)
          = fejerW K k * (2 * (∑ j, ε j * Real.cos (2*Real.pi*k*θ j))^2) by ring]
    rw [two_mul_sq_sum ε θ (2*Real.pi*k)]
    simp only [Finset.mul_sum]
  rw [Finset.sum_congr rfl hstep]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro j _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro l _
  rw [fejerT, fejerT]
  rw [show (∑ x ∈ Finset.Icc 1 K, fejerW K x * (ε j * ε l * (Real.cos (2*Real.pi*x*(θ j + θ l)) + Real.cos (2*Real.pi*x*(θ j - θ l)))))
      = ε j * ε l * ∑ x ∈ Finset.Icc 1 K, fejerW K x * (Real.cos (2*Real.pi*x*(θ j + θ l)) + Real.cos (2*Real.pi*x*(θ j - θ l))) by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl; intro x _; ring]
  congr 1
  rw [Finset.sum_congr rfl (fun x _ => mul_add (fejerW K x) _ _), Finset.sum_add_distrib]

theorem fejer_sum_cos_sq_ge {n : ℕ} (ε θ : Fin n → ℝ) (K : ℕ) (hε0 : ∀ j, 0 ≤ ε j) :
    ((K:ℝ)+1)/4 * (∑ j, (ε j)^2) - (1/2) * (∑ j, ε j)^2
      ≤ ∑ k ∈ Finset.Icc 1 K, fejerW K k *
          (∑ j, ε j * Real.cos (2*Real.pi*k*θ j))^2 := by
  -- Off-diagonal pairs are bounded by `-ε_j ε_l` and the diagonal gains `(K+1)/2 · ε_j^2`.
  have hpoint : ∀ j l : Fin n, -(ε j * ε l) + (if j = l then (ε j)^2 * ((K:ℝ)+1)/2 else 0)
      ≤ ε j * ε l * (fejerT K (θ j + θ l) + fejerT K (θ j - θ l)) := by
    intro j l
    have hj : 0 ≤ ε j := hε0 j
    have hl : 0 ≤ ε l := hε0 l
    rcases eq_or_ne j l with hjl | hjl
    · subst hjl
      rw [ite_eq_left rfl, sub_self, fejerT_zero]
      have h1 : -(1/2:ℝ) ≤ fejerT K (θ j + θ j) := fejerT_ge K _
      have hnonneg : 0 ≤ ε j * ε j := mul_nonneg hj hj
      nlinarith [mul_le_mul_of_nonneg_left h1 hnonneg]
    · rw [ite_eq_right hjl, add_zero]
      have h1 : -(1/2:ℝ) ≤ fejerT K (θ j + θ l) := fejerT_ge K _
      have h2 : -(1/2:ℝ) ≤ fejerT K (θ j - θ l) := fejerT_ge K _
      have hnonneg : 0 ≤ ε j * ε l := mul_nonneg hj hl
      nlinarith [mul_le_mul_of_nonneg_left
        (by linarith : -(1/2:ℝ) + -(1/2) ≤ fejerT K (θ j + θ l) + fejerT K (θ j - θ l)) hnonneg]
  -- The lower bounding double sum evaluates to `(K+1)/2 · ∑ ε_j^2 - (∑ ε_j)^2`.
  have hLHS : ∑ j, ∑ l, (-(ε j * ε l) + (if j = l then (ε j)^2 * ((K:ℝ)+1)/2 else 0))
      = ((K:ℝ)+1)/2 * (∑ j, (ε j)^2) - (∑ j, ε j)^2 := by
    have h1 : ∀ j : Fin n, (∑ l, (-(ε j * ε l) + (if j = l then (ε j)^2 * ((K:ℝ)+1)/2 else 0)))
        = -(ε j * ∑ l, ε l) + (ε j)^2 * ((K:ℝ)+1)/2 := by
      intro j
      rw [Finset.sum_add_distrib, Finset.sum_neg_distrib, Finset.mul_sum, Finset.sum_ite_eq]
      simp
    rw [Finset.sum_congr rfl (fun j _ => h1 j)]
    rw [Finset.sum_add_distrib, Finset.sum_neg_distrib]
    rw [← Finset.sum_mul, ← Finset.sum_div, ← Finset.sum_mul]
    ring
  have hsum : ∑ j, ∑ l, (-(ε j * ε l) + (if j = l then (ε j)^2 * ((K:ℝ)+1)/2 else 0))
      ≤ ∑ j, ∑ l, ε j * ε l * (fejerT K (θ j + θ l) + fejerT K (θ j - θ l)) := by
    apply Finset.sum_le_sum; intro j _
    apply Finset.sum_le_sum; intro l _
    exact hpoint j l
  have h2 := fejer_expand ε θ K
  suffices h : ((K:ℝ)+1)/2 * (∑ j, (ε j)^2) - (∑ j, ε j)^2
      ≤ 2 * (∑ k ∈ Finset.Icc 1 K, fejerW K k * (∑ j, ε j * Real.cos (2*Real.pi*k*θ j))^2) by
    linarith
  rw [h2, ← hLHS]
  exact hsum

end Work.BW
