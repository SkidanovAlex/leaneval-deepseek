import Mathlib
import Submission.Work.LinnikAreas.Density4.prime_weight_pointwise
import Submission.Work.LinnikAreas.Density4.sqrt_delta_telescope

namespace Work.LinnikAreas.Density4

/-- For `n ≥ 2`, the summand `1/(n √n)` telescopes against `1/√·`. -/
lemma delta_nonneg (n : ℕ) (hn : 2 ≤ n) :
    0 ≤ 1 / Real.sqrt ((n : ℝ) - 1) - 1 / Real.sqrt (n : ℝ) := by
  have hn2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hpos1 : 0 < Real.sqrt ((n : ℝ) - 1) := Real.sqrt_pos_of_pos (by linarith)
  have hpos2 : 0 < Real.sqrt ((n : ℝ)) := Real.sqrt_pos_of_pos (by linarith)
  have hle : Real.sqrt ((n : ℝ) - 1) ≤ Real.sqrt ((n : ℝ)) := Real.sqrt_le_sqrt (by linarith)
  have h := one_div_le_one_div_of_le hpos1 hle
  linarith

theorem sum_prime_sqrt_weight_le (M : ℕ) :
    (∑ p ∈ (Finset.Icc 2 M).filter Nat.Prime,
        2 / ((p : ℝ) * ((p : ℝ) - 1)) * Real.sqrt (p : ℝ)) ≤ 16 := by
  rcases lt_or_ge M 2 with hM | hM
  · have hI : Finset.Icc 2 M = ∅ := Finset.Icc_eq_empty_of_lt hM
    rw [hI]
    simp
  · have h₁ : ∑ p ∈ (Finset.Icc 2 M).filter Nat.Prime,
          (2 / ((p : ℝ) * ((p : ℝ) - 1)) * Real.sqrt (p : ℝ))
        ≤ ∑ p ∈ (Finset.Icc 2 M).filter Nat.Prime,
          (8 * (1 / Real.sqrt ((p : ℝ) - 1) - 1 / Real.sqrt (p : ℝ))) := by
      apply Finset.sum_le_sum
      intro p hp
      simp only [Finset.mem_filter, Finset.mem_Icc] at hp
      exact prime_weight_pointwise p hp.1.1
    have h₂ : ∑ p ∈ (Finset.Icc 2 M).filter Nat.Prime,
          (8 * (1 / Real.sqrt ((p : ℝ) - 1) - 1 / Real.sqrt (p : ℝ)))
        ≤ ∑ n ∈ Finset.Icc 2 M,
          (8 * (1 / Real.sqrt ((n : ℝ) - 1) - 1 / Real.sqrt (n : ℝ))) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset Nat.Prime _)
      intro n hn _
      simp only [Finset.mem_Icc] at hn
      have := delta_nonneg n hn.1
      linarith
    have h₃ : ∑ n ∈ Finset.Icc 2 M,
          (8 * (1 / Real.sqrt ((n : ℝ) - 1) - 1 / Real.sqrt (n : ℝ)))
        = 8 * (1 - 1 / Real.sqrt (M : ℝ)) := by
      rw [← Finset.mul_sum, sqrt_delta_telescope M hM]
    calc ∑ p ∈ (Finset.Icc 2 M).filter Nat.Prime,
            (2 / ((p : ℝ) * ((p : ℝ) - 1)) * Real.sqrt (p : ℝ))
        ≤ ∑ p ∈ (Finset.Icc 2 M).filter Nat.Prime,
            (8 * (1 / Real.sqrt ((p : ℝ) - 1) - 1 / Real.sqrt (p : ℝ))) := h₁
      _ ≤ ∑ n ∈ Finset.Icc 2 M,
            (8 * (1 / Real.sqrt ((n : ℝ) - 1) - 1 / Real.sqrt (n : ℝ))) := h₂
      _ = 8 * (1 - 1 / Real.sqrt (M : ℝ)) := h₃
      _ ≤ 8 := by
          have : 0 ≤ 1 / Real.sqrt (M : ℝ) := by positivity
          linarith
      _ ≤ 16 := by norm_num

end Work.LinnikAreas.Density4
