import Mathlib
import Submission.Commons.Analysis.Series.sum_Icc_inv_mul_sqrt_le_three

namespace Commons.Analysis.Abel

open Finset

/-- **Summation by parts** in the form used below: for `F G : ℕ → ℝ` and `n : ℕ`,
`∑_{i<n} F i * G i = F (n-1) * (∑_{i<n} G i) + ∑_{i<n-1} (F i - F (i+1)) * (∑_{j<i+1} G j)`.
This is `Finset.sum_range_by_parts` with the sign of the correction term flipped. -/
lemma sum_range_by_parts_mul (F G : ℕ → ℝ) (n : ℕ) :
    ∑ i ∈ Finset.range n, F i * G i =
      F (n - 1) * (∑ i ∈ Finset.range n, G i)
        + ∑ i ∈ Finset.range (n - 1), (F i - F (i + 1)) * (∑ i ∈ Finset.range (i + 1), G i) := by
  have h := Finset.sum_range_by_parts F G n
  simp only [smul_eq_mul] at h
  rw [h]
  rw [show (∑ i ∈ Finset.range (n - 1), (F i - F (i + 1)) * (∑ i ∈ Finset.range (i + 1), G i))
        = - (∑ i ∈ Finset.range (n - 1),
              (F (i + 1) - F i) * (∑ i ∈ Finset.range (i + 1), G i)) from by
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro i _
      ring]
  ring

theorem summation_by_parts (f g : ℕ → ℝ) (y : ℕ) :
    (∑ m ∈ Finset.Icc 1 y, f m * g m)
      = f y * (∑ m ∈ Finset.Icc 1 y, g m)
        + ∑ m ∈ Finset.Icc 1 (y - 1), (f m - f (m + 1)) * (∑ k ∈ Finset.Icc 1 m, g k) := by
  rcases y with _ | y
  · simp
  · rw [show y + 1 - 1 = y by omega]
    simp only [Commons.Analysis.Series.sum_Icc_one_eq_sum_range]
    rw [sum_range_by_parts_mul (fun i => f (i + 1)) (fun i => g (i + 1)) (y + 1),
      show y + 1 - 1 = y by omega]

end Commons.Analysis.Abel
