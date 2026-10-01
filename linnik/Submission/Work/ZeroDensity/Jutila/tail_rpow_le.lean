import Mathlib
import Submission.Work.ZeroDensity.Jutila.JutilaDefs

namespace Work.ZeroDensity.Jutila

/-- Comparison of the tail of the series `∑ n^{-σ}` with the integral
`∫_i^∞ x^{-σ} dx = i^{1-σ}/(σ-1)`.  For `σ > 1` and `i ≥ 1`,
`∑_{n = i+1}^{N-1} n^{-σ} ≤ i^{1-σ}/(σ-1)`. -/
theorem tail_rpow_le (σ : ℝ) (hσ : 1 < σ) (i N : ℕ) (hi : 1 ≤ i) :
    ∑ n ∈ Finset.Ico (i + 1) N, (n : ℝ) ^ (-σ) ≤ (i : ℝ) ^ (1 - σ) / (σ - 1) := by
  have hi_pos : (0 : ℝ) < i := by exact_mod_cast hi
  -- Antitonicity of `x ↦ x ^ (-σ)` on `[i, N]`, inherited from `(0, ∞)`.
  have hAnti : AntitoneOn (fun x : ℝ => x ^ (-σ)) (Set.Icc (i : ℝ) (N : ℝ)) := by
    refine (Real.antitoneOn_rpow_Ioi_of_exponent_nonpos (by linarith : -σ ≤ 0)).mono ?_
    intro x hx
    simp only [Set.mem_Icc] at hx
    simp only [Set.mem_Ioi]
    linarith [hx.1]
  have hIntble : MeasureTheory.IntegrableOn (fun x : ℝ => x ^ (-σ)) (Set.Ioi (i : ℝ)) :=
    integrableOn_Ioi_rpow_of_lt (by linarith : -σ < -1) hi_pos
  have hnonneg : ∀ t ∈ Set.Ioi (i : ℝ), 0 ≤ t ^ (-σ) := by
    intro t ht
    exact Real.rpow_nonneg (le_of_lt (hi_pos.trans (Set.mem_Ioi.mp ht))) _
  -- Value of the improper integral.
  have hInt : ∫ x in Set.Ioi (i : ℝ), x ^ (-σ) = (i : ℝ) ^ (1 - σ) / (σ - 1) := by
    rw [integral_Ioi_rpow_of_lt (by linarith : -σ < -1) hi_pos]
    rw [show -σ + 1 = 1 - σ by ring]
    rw [show (1 : ℝ) - σ = -(σ - 1) by ring]
    rw [div_neg, neg_div, neg_neg]
  -- Sum/integral comparison, with the summation reindexed by `n ↦ n + 1`.
  calc ∑ n ∈ Finset.Ico (i + 1) N, (n : ℝ) ^ (-σ)
      ≤ ∑ n ∈ Finset.Ico (i + 1) (N + 1), (n : ℝ) ^ (-σ) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro x hx; simp only [Finset.mem_Ico] at hx ⊢; omega
        · intro x _ _; exact Real.rpow_nonneg (Nat.cast_nonneg x) _
    _ = ∑ n ∈ Finset.Ico i N, ((n + 1 : ℕ) : ℝ) ^ (-σ) := by
        rw [Finset.sum_Ico_add' (fun x : ℕ => (x : ℝ) ^ (-σ)) i N 1]
    _ ≤ ∫ x in Set.Ioi (i : ℝ), x ^ (-σ) :=
        AntitoneOn.sum_Ico_le_integral hAnti hIntble hnonneg
    _ = (i : ℝ) ^ (1 - σ) / (σ - 1) := hInt

end Work.ZeroDensity.Jutila
