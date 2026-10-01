import Mathlib
import Submission.Work.LinnikAreas.JMAux.GeomIndicatorSum

namespace Work.LinnikAreas.JMAux

lemma GeomTailLe (r : ℝ) (hr0 : 0 ≤ r) (hr : r ≤ 3/4) (N j : ℕ) :
    ∑ k ∈ Finset.range N, (if j ≤ k then (1:ℝ) else 0) * r^k ≤ 4 * r^j := by
  have hr1 : r < 1 := by linarith
  have hrpow : 0 ≤ r ^ j := pow_nonneg hr0 j
  -- Rewrite the indicator times the term.
  have hS : ∑ k ∈ Finset.range N, (if j ≤ k then (1:ℝ) else 0) * r^k
          = ∑ k ∈ Finset.range N, (if j ≤ k then r^k else 0) := by
    apply Finset.sum_congr rfl
    intro k _
    by_cases h : j ≤ k
    · rw [if_pos h, if_pos h, one_mul]
    · rw [if_neg h, if_neg h, zero_mul]
  rw [hS]
  rcases lt_or_ge j N with hjN | hNj
  · -- If `j < N`, factor out `r^j` and bound the remaining geometric series.
    have hshift : ∑ k ∈ Finset.range N, (if j ≤ k then r ^ k else 0)
        = r ^ j * ∑ k ∈ Finset.range N, (if j ≤ k then r ^ (k - j) else 0) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      by_cases h : j ≤ k
      · rw [if_pos h, if_pos h, ← pow_add, Nat.add_sub_of_le h]
      · rw [if_neg h, if_neg h, mul_zero]
    rw [hshift]
    have hT : ∑ k ∈ Finset.range N, (if j ≤ k then r ^ (k - j) else 0)
            = ∑ i ∈ Finset.range (N - j), r ^ i := by
      rw [← Finset.sum_filter (s := Finset.range N) (fun k => j ≤ k) (fun k => r ^ (k - j))]
      have hfilt : (Finset.range N).filter (fun k => j ≤ k) = Finset.Ico j N := by
        ext x; simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]; omega
      rw [hfilt, Finset.sum_Ico_eq_sum_range]
      apply Finset.sum_congr rfl
      intro i _
      rw [Nat.add_sub_cancel_left]
    rw [hT]
    have hTle : ∑ i ∈ Finset.range (N - j), r ^ i ≤ (1 - r)⁻¹ :=
      geom_sum_range_le_inv hr0 hr1 (N - j)
    have hinv : (1 - r)⁻¹ ≤ 4 := by
      have h1r : 0 < 1 - r := by linarith
      rw [inv_le_iff_one_le_mul₀ h1r]
      nlinarith [hr]
    calc r ^ j * ∑ i ∈ Finset.range (N - j), r ^ i
        ≤ r ^ j * (1 - r)⁻¹ := mul_le_mul_of_nonneg_left hTle hrpow
      _ ≤ r ^ j * 4 := mul_le_mul_of_nonneg_left hinv hrpow
      _ = 4 * r ^ j := by ring
  · -- If `N ≤ j` the sum is empty.
    have hzero : ∑ k ∈ Finset.range N, (if j ≤ k then r ^ k else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro k hk
      rw [Finset.mem_range] at hk
      rw [if_neg]
      omega
    rw [hzero]
    linarith

end Work.LinnikAreas.JMAux
