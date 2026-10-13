import Mathlib
import Submission.Work.WilC4aP.Basic
import Submission.Work.WilC4aP.PzAlg

namespace Work.WilC4aP

open Polynomial

/-- For `0 ≤ x ≤ 1` and `N > 0`, `x ^ N ≤ x`. -/
private lemma pow_le_self_of_le_one {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) {N : ℕ} (hN : 0 < N) :
    x ^ N ≤ x := by
  rw [show N = (N - 1) + 1 by omega, pow_succ]
  exact mul_le_of_le_one_left hx0 (pow_le_one₀ hx0 hx1)

/-- The value of the first block of `combineFamily`. -/
@[simp] lemma combineFamily_inl {k n N₁ N₂ : ℕ} (η₁ : Fin k → ℂ → ℂ) (η₂ : Fin n → ℂ → ℂ)
    (i : Fin k) (u : ℂ) :
    combineFamily N₁ N₂ η₁ η₂ (finSumFinEquiv (Sum.inl i)) u = η₁ i (u ^ N₂) := by
  simp [combineFamily]

/-- The value of the second block of `combineFamily`. -/
@[simp] lemma combineFamily_inr {k n N₁ N₂ : ℕ} (η₁ : Fin k → ℂ → ℂ) (η₂ : Fin n → ℂ → ℂ)
    (i : Fin n) (u : ℂ) :
    combineFamily N₁ N₂ η₁ η₂ (finSumFinEquiv (Sum.inr i)) u = η₂ i (u ^ N₁) := by
  simp [combineFamily]

lemma branches_mul {k n N₁ N₂ : ℕ} (hN₁ : 0 < N₁) (hN₂ : 0 < N₂)
    {G H : Polynomial (ℂ → ℂ)} (η₁ : Fin k → ℂ → ℂ) (η₂ : Fin n → ℂ → ℂ)
    {ρ₁ ρ₂ : ℝ} (hρ₁ : 0 < ρ₁) (hρ₂ : 0 < ρ₂)
    (h₁ : ∀ u ∈ Metric.ball (0 : ℂ) ρ₁,
      Pz G (u ^ N₁) = ∏ j, (Polynomial.X - Polynomial.C (η₁ j u)))
    (h₂ : ∀ u ∈ Metric.ball (0 : ℂ) ρ₂,
      Pz H (u ^ N₂) = ∏ j, (Polynomial.X - Polynomial.C (η₂ j u))) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ u ∈ Metric.ball (0 : ℂ) ρ,
      Pz (G * H) (u ^ (N₁ * N₂)) =
        ∏ j, (Polynomial.X - Polynomial.C (combineFamily N₁ N₂ η₁ η₂ j u)) := by
  refine ⟨min 1 (min ρ₁ ρ₂), lt_min one_pos (lt_min hρ₁ hρ₂), ?_⟩
  intro u hu
  have huρ : ‖u‖ < min 1 (min ρ₁ ρ₂) := by
    have h := Metric.mem_ball.mp hu
    rwa [dist_eq_norm, sub_zero] at h
  have hu1 : ‖u‖ ≤ 1 := le_of_lt (lt_of_lt_of_le huρ (min_le_left _ _))
  have huρ₁ : ‖u‖ < ρ₁ :=
    lt_of_lt_of_le huρ (le_trans (min_le_right _ _) (min_le_left _ _))
  have huρ₂ : ‖u‖ < ρ₂ :=
    lt_of_lt_of_le huρ (le_trans (min_le_right _ _) (min_le_right _ _))
  have hmem₁ : u ^ N₂ ∈ Metric.ball (0 : ℂ) ρ₁ := by
    rw [Metric.mem_ball, dist_eq_norm, sub_zero, norm_pow]
    exact lt_of_le_of_lt (pow_le_self_of_le_one (norm_nonneg u) hu1 hN₂) huρ₁
  have hmem₂ : u ^ N₁ ∈ Metric.ball (0 : ℂ) ρ₂ := by
    rw [Metric.mem_ball, dist_eq_norm, sub_zero, norm_pow]
    exact lt_of_le_of_lt (pow_le_self_of_le_one (norm_nonneg u) hu1 hN₁) huρ₂
  have e1 : u ^ (N₁ * N₂) = (u ^ N₂) ^ N₁ := by
    rw [← pow_mul, Nat.mul_comm N₁ N₂]
  have e2 : u ^ (N₁ * N₂) = (u ^ N₁) ^ N₂ := by rw [pow_mul]
  have hG : Pz G (u ^ (N₁ * N₂)) = ∏ j : Fin k, (X - C (η₁ j (u ^ N₂))) := by
    rw [e1]; exact h₁ (u ^ N₂) hmem₁
  have hH : Pz H (u ^ (N₁ * N₂)) = ∏ j : Fin n, (X - C (η₂ j (u ^ N₁))) := by
    rw [e2]; exact h₂ (u ^ N₁) hmem₂
  rw [Pz_mul, hG, hH,
    prod_fin_add (fun j : Fin (k + n) => (X - C (combineFamily N₁ N₂ η₁ η₂ j u)))]
  simp only [combineFamily_inl, combineFamily_inr]

end Work.WilC4aP
