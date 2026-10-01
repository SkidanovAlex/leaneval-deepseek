import Mathlib

namespace Work.ZeroDensity.Ingham

/-- Off-diagonal kernel sum bound: the double sum of `b m * conj (b n) * K m n`
over distinct indices `m ≠ n` in `Icc 1 N` is dominated (up to a factor `2`) by the
corresponding double sum of the absolute values with the kernel weight
`max m n / |m - n|`. -/
lemma offdiag_kernel_sum_bound (b : ℕ → ℂ) (N : ℕ) (K : ℕ → ℕ → ℂ)
    (hK : ∀ m n, m ∈ Finset.Icc 1 N → n ∈ Finset.Icc 1 N → m ≠ n →
      ‖K m n‖ ≤ 2 * max (m : ℝ) (n : ℝ) / |(m : ℝ) - (n : ℝ)|) :
    ‖∑ m ∈ Finset.Icc 1 N, ∑ n ∈ (Finset.Icc 1 N).erase m,
        (b m * (starRingEnd ℂ) (b n)) * K m n‖
      ≤ 2 * ∑ m ∈ Finset.Icc 1 N, ∑ n ∈ Finset.Icc 1 N,
          ‖b m‖ * ‖b n‖ * (max (m : ℝ) (n : ℝ)) / |(m : ℝ) - (n : ℝ)| := by
  set S : Finset ℕ := Finset.Icc 1 N
  -- Nonnegativity of the comparison weight `g m n = ‖b m‖ * ‖b n‖ * max m n / |m - n|`.
  have hnonneg : ∀ m n : ℕ,
      0 ≤ ‖b m‖ * ‖b n‖ * (max (m : ℝ) (n : ℝ)) / |(m : ℝ) - (n : ℝ)| := by
    intro m n
    apply div_nonneg
    · exact mul_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _))
        (le_trans (Nat.cast_nonneg n) (le_max_right _ _))
    · exact abs_nonneg _
  -- Bound the inner (off-diagonal) sum for each fixed `m`.
  have hinner : ∀ m ∈ S, ‖∑ n ∈ S.erase m, (b m * (starRingEnd ℂ) (b n)) * K m n‖
      ≤ 2 * ∑ n ∈ S, ‖b m‖ * ‖b n‖ * (max (m : ℝ) (n : ℝ)) / |(m : ℝ) - (n : ℝ)| := by
    intro m hm
    calc
      ‖∑ n ∈ S.erase m, (b m * (starRingEnd ℂ) (b n)) * K m n‖
          ≤ ∑ n ∈ S.erase m, ‖(b m * (starRingEnd ℂ) (b n)) * K m n‖ :=
            norm_sum_le _ _
      _ = ∑ n ∈ S.erase m, ‖b m‖ * ‖b n‖ * ‖K m n‖ := by
            apply Finset.sum_congr rfl
            intro n _
            rw [norm_mul, norm_mul, starRingEnd_apply, norm_star]
      _ ≤ ∑ n ∈ S.erase m,
            ‖b m‖ * ‖b n‖ * (2 * max (m : ℝ) (n : ℝ) / |(m : ℝ) - (n : ℝ)|) := by
            apply Finset.sum_le_sum
            intro n hn
            obtain ⟨hnm, hnS⟩ := Finset.mem_erase.mp hn
            have h1 := hK m n hm hnS (Ne.symm hnm)
            exact mul_le_mul_of_nonneg_left h1 (mul_nonneg (norm_nonneg _) (norm_nonneg _))
      _ = 2 * ∑ n ∈ S.erase m,
            ‖b m‖ * ‖b n‖ * (max (m : ℝ) (n : ℝ)) / |(m : ℝ) - (n : ℝ)| := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro n _
            ring
      _ ≤ 2 * ∑ n ∈ S, ‖b m‖ * ‖b n‖ * (max (m : ℝ) (n : ℝ)) / |(m : ℝ) - (n : ℝ)| := by
            apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 2)
            apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset m S)
            intro n _ _
            exact hnonneg m n
  calc
    ‖∑ m ∈ S, ∑ n ∈ S.erase m, (b m * (starRingEnd ℂ) (b n)) * K m n‖
        ≤ ∑ m ∈ S, ‖∑ n ∈ S.erase m, (b m * (starRingEnd ℂ) (b n)) * K m n‖ :=
          norm_sum_le _ _
    _ ≤ ∑ m ∈ S, 2 * ∑ n ∈ S,
          ‖b m‖ * ‖b n‖ * (max (m : ℝ) (n : ℝ)) / |(m : ℝ) - (n : ℝ)| :=
          Finset.sum_le_sum hinner
    _ = 2 * ∑ m ∈ S, ∑ n ∈ S,
          ‖b m‖ * ‖b n‖ * (max (m : ℝ) (n : ℝ)) / |(m : ℝ) - (n : ℝ)| := by
          rw [Finset.mul_sum]

end Work.ZeroDensity.Ingham
