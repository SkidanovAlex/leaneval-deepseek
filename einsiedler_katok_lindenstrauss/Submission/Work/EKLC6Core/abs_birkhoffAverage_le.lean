import Mathlib

namespace Work.EKLC6Core

theorem abs_birkhoffAverage_le {X : Type*} (T : X → X) (g : X → ℝ) (B : ℝ) (hB : 0 ≤ B)
    (hg : ∀ x, |g x| ≤ B) (n : ℕ) (x : X) :
    |birkhoffAverage ℝ T g n x| ≤ B := by
  rw [birkhoffAverage, birkhoffSum, smul_eq_mul]
  by_cases hn : n = 0
  · subst hn
    simp
    exact hB
  · have hnR : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn
    have hinvnn : 0 ≤ (n : ℝ)⁻¹ := inv_nonneg.mpr (Nat.cast_nonneg n)
    rw [abs_mul, abs_of_nonneg hinvnn]
    have hS : |∑ k ∈ Finset.range n, g (T^[k] x)| ≤ (n : ℝ) * B := by
      calc |∑ k ∈ Finset.range n, g (T^[k] x)|
          ≤ ∑ k ∈ Finset.range n, |g (T^[k] x)| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ k ∈ Finset.range n, B := Finset.sum_le_sum (fun k _ => hg _)
        _ = (n : ℝ) * B := by simp [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    calc (n : ℝ)⁻¹ * |∑ k ∈ Finset.range n, g (T^[k] x)|
        ≤ (n : ℝ)⁻¹ * ((n : ℝ) * B) := mul_le_mul_of_nonneg_left hS hinvnn
      _ = B := by rw [← mul_assoc, inv_mul_cancel₀ hnR, one_mul]

end Work.EKLC6Core
