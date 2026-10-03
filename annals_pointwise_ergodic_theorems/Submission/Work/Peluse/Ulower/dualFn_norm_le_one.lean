import Mathlib
import Submission.Work.Peluse.Basic

namespace Work.Peluse.Ulower

open scoped BigOperators

/-- The dual function `F₂(x) = E_{y ∈ [N]} f₀ (x - P(y)) f₁ (x + y - P(y))` is bounded by `1`
in sup norm as soon as `f₀` and `f₁` are bounded by `1` in sup norm and `N ≥ 1`
(the average is a genuine average, not a sum). -/
theorem dualFn_norm_le_one {N : ℕ} (hN : 1 ≤ N) (P : Polynomial ℤ) (f₀ f₁ : ℤ → ℂ)
    (h0 : ∀ x : ℤ, ‖f₀ x‖ ≤ 1) (h1 : ∀ x : ℤ, ‖f₁ x‖ ≤ 1) :
    ∀ x : ℤ, ‖Work.Peluse.dualFn N P f₀ f₁ x‖ ≤ 1 := by
  intro x
  have hNpos : (0 : ℝ) < N := by
    exact_mod_cast (Nat.lt_of_lt_of_le Nat.zero_lt_one hN)
  have hNne : (N : ℝ) ≠ 0 := ne_of_gt hNpos
  have hcard : ((Finset.Icc 1 N).card : ℝ) = (N : ℝ) := by
    rw [Nat.card_Icc]
    have h : N + 1 - 1 = N := by omega
    rw [h]
  have hsum : (∑ _y ∈ Finset.Icc 1 N, (1 : ℝ)) = (N : ℝ) := by
    rw [Finset.sum_const, nsmul_eq_mul, mul_one, hcard]
  have hterm : ∀ y ∈ Finset.Icc 1 N,
      ‖f₀ (x - P.eval (y : ℤ)) * f₁ (x + (y : ℤ) - P.eval (y : ℤ))‖ ≤ 1 := by
    intro y _
    rw [norm_mul]
    have ha := h0 (x - P.eval (y : ℤ))
    have hb := h1 (x + (y : ℤ) - P.eval (y : ℤ))
    have hna : (0 : ℝ) ≤ ‖f₀ (x - P.eval (y : ℤ))‖ := norm_nonneg _
    have hnb : (0 : ℝ) ≤ ‖f₁ (x + (y : ℤ) - P.eval (y : ℤ))‖ := norm_nonneg _
    nlinarith [ha, hb, hna, hnb]
  show ‖((N : ℂ))⁻¹ * ∑ y ∈ Finset.Icc 1 N,
      f₀ (x - P.eval (y : ℤ)) * f₁ (x + (y : ℤ) - P.eval (y : ℤ))‖ ≤ 1
  calc ‖((N : ℂ))⁻¹ * ∑ y ∈ Finset.Icc 1 N,
        f₀ (x - P.eval (y : ℤ)) * f₁ (x + (y : ℤ) - P.eval (y : ℤ))‖
      ≤ ‖((N : ℂ))⁻¹‖ * ‖∑ y ∈ Finset.Icc 1 N,
        f₀ (x - P.eval (y : ℤ)) * f₁ (x + (y : ℤ) - P.eval (y : ℤ))‖ := norm_mul_le _ _
    _ = ((N : ℝ))⁻¹ * ‖∑ y ∈ Finset.Icc 1 N,
        f₀ (x - P.eval (y : ℤ)) * f₁ (x + (y : ℤ) - P.eval (y : ℤ))‖ := by
        rw [norm_inv, Complex.norm_natCast]
    _ ≤ ((N : ℝ))⁻¹ * (∑ y ∈ Finset.Icc 1 N,
        ‖f₀ (x - P.eval (y : ℤ)) * f₁ (x + (y : ℤ) - P.eval (y : ℤ))‖) := by
        exact mul_le_mul_of_nonneg_left (norm_sum_le _ _) (by positivity)
    _ ≤ ((N : ℝ))⁻¹ * (∑ y ∈ Finset.Icc 1 N, (1 : ℝ)) := by
        exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum hterm) (by positivity)
    _ = ((N : ℝ))⁻¹ * (N : ℝ) := by rw [hsum]
    _ = 1 := inv_mul_cancel₀ hNne

end Work.Peluse.Ulower
