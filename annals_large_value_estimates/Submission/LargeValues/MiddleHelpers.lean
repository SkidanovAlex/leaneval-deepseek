import Submission.LargeValues.Pieces

open LargeValueEstimates
open Asymptotics Complex
set_option autoImplicit false

namespace Submission.LargeValues

/-- Sharp bound on the rescaled lengths: `N_i ≤ 3N/2`. -/
theorem scaledN_le_three_halves (N : ℕ) {i : ℕ} (hi : i < 3) :
    (scaledN N i : ℝ) ≤ 3 * (N : ℝ) / 2 := by
  have c2 : 6 * ((5 * N / 6 : ℕ) : ℝ) ≤ 5 * (N : ℝ) := by exact_mod_cast mul_div_le_six N
  have c4 : 2 * ((3 * N / 2 : ℕ) : ℝ) ≤ 3 * (N : ℝ) := by exact_mod_cast mul_div_le_two N
  interval_cases i
  · have h0 : scaledN N 0 = 5 * N / 6 := by simp [scaledN]
    rw [h0]; linarith
  · have h0 : scaledN N 1 = N := by simp [scaledN]
    rw [h0]; linarith [Nat.cast_nonneg (α := ℝ) N]
  · have h0 : scaledN N 2 = 3 * N / 2 := by simp [scaledN]
    rw [h0]; linarith

/-- `(3/2)^{7/10} < 4/3`. -/
theorem rpow_three_halves_lt : ((3 : ℝ) / 2) ^ (7 / 10 : ℝ) < 4 / 3 := by
  have h1 : (((3 : ℝ) / 2) ^ (7 / 10 : ℝ)) ^ 10 = ((3 : ℝ) / 2) ^ 7 := by
    rw [← Real.rpow_natCast (((3 : ℝ) / 2) ^ (7 / 10 : ℝ)) 10,
      ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3 / 2)]
    norm_num
  have h2 : ((3 : ℝ) / 2) ^ 7 < ((4 : ℝ) / 3) ^ 10 := by norm_num
  have h3 : (0 : ℝ) ≤ ((3 : ℝ) / 2) ^ (7 / 10 : ℝ) := Real.rpow_nonneg (by norm_num) _
  have h4 : (((3 : ℝ) / 2) ^ (7 / 10 : ℝ)) ^ 10 < ((4 : ℝ) / 3) ^ 10 := by
    rw [h1]; exact h2
  exact lt_of_pow_lt_pow_left₀ 10 (by norm_num : (0 : ℝ) ≤ 4 / 3) h4

/-- `2^{4/5} ≤ 3`. -/
theorem rpow_two_four_fifths_le : ((2 : ℝ)) ^ (4 / 5 : ℝ) ≤ 3 := by
  by_contra hc
  rw [not_le] at hc
  have h1 : ((2 : ℝ) ^ (4 / 5 : ℝ)) ^ 5 = ((2 : ℝ)) ^ 4 := by
    rw [← Real.rpow_natCast ((2 : ℝ) ^ (4 / 5 : ℝ)) 5,
      ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  have h2 : (3 : ℝ) ^ 5 < ((2 : ℝ) ^ (4 / 5 : ℝ)) ^ 5 :=
    pow_lt_pow_left₀ hc (by norm_num : (0 : ℝ) ≤ 3) (by norm_num : (5 : ℕ) ≠ 0)
  rw [h1] at h2
  norm_num at h2

/-- `(1/3) ≤ (1/2)^{4/5}`, equivalently `2^{4/5} ≤ 3`. -/
theorem one_third_le_half_rpow : (1 / 3 : ℝ) ≤ ((1 : ℝ) / 2) ^ (4 / 5 : ℝ) := by
  have h : (1 / 3 : ℝ) ≤ ((2 : ℝ) ^ (4 / 5 : ℝ))⁻¹ := by
    rw [inv_eq_one_div, le_div_iff₀ (Real.rpow_pos_of_pos (by norm_num) _)]
    linarith [rpow_two_four_fifths_le]
  have h2 : ((2 : ℝ) ^ (4 / 5 : ℝ))⁻¹ = ((1 : ℝ) / 2) ^ (4 / 5 : ℝ) := by
    rw [← Real.inv_rpow (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  rwa [h2] at h

/-- Rewriting lemma: the smoothed polynomial with the phase `a` absorbed into the coefficients
restricted to the `i`-th piece is exactly the `i`-th piece sum. -/
theorem smoothedPoly_pieceSum {N : ℕ} (hN : 6 ≤ N) {i : ℕ} (hi : i < 3) (b : ℕ → ℂ)
    {t a : ℝ} :
    smoothedPoly (scaledN N i)
      (fun n => if n ∈ pieceSet N i then b n * (n : ℂ) ^ (I * (a : ℂ)) else 0) (t - a)
      = pieceSum N i b t := by
  classical
  have hsub : pieceSet N i ⊆ Finset.Icc (scaledN N i) (2 * scaledN N i) :=
    fun n hn => pieceSet_subset_Icc hN hi hn
  have hnpos : ∀ n ∈ pieceSet N i, (n : ℂ) ≠ 0 := by
    intro n hn
    have hnIcc : n ∈ Finset.Icc N (2 * N) := (Finset.mem_filter.mp hn).1
    have hNn : N ≤ n := (Finset.mem_Icc.mp hnIcc).1
    have : (0 : ℕ) < n := by omega
    exact_mod_cast Nat.pos_iff_ne_zero.mp this
  unfold smoothedPoly pieceSum
  have hterm : ∀ n ∈ Finset.Icc (scaledN N i) (2 * scaledN N i),
      ((bumpW ((n : ℝ) / (scaledN N i : ℝ))) : ℂ)
        * (if n ∈ pieceSet N i then b n * (n : ℂ) ^ (I * (a : ℂ)) else 0)
        * (n : ℂ) ^ (I * ((t - a : ℝ) : ℂ))
      = (if n ∈ pieceSet N i then b n * (n : ℂ) ^ (I * (t : ℂ)) else 0) := by
    intro n hn
    by_cases hmem : n ∈ pieceSet N i
    · rw [if_pos hmem, if_pos hmem]
      have hw : bumpW ((n : ℝ) / (scaledN N i : ℝ)) = 1 := by
        apply bumpW_eq_one
        exact pieceSet_window hN hi hmem
      rw [hw]
      push_cast
      rw [show (1 : ℂ) * (b n * (n : ℂ) ^ (I * (a : ℂ))) * (n : ℂ) ^ (I * ((t : ℂ) - (a : ℂ)))
            = b n * ((n : ℂ) ^ (I * (a : ℂ)) * (n : ℂ) ^ (I * ((t : ℂ) - (a : ℂ)))) by ring]
      rw [← Complex.cpow_add (I * (a : ℂ)) (I * ((t : ℂ) - (a : ℂ))) (hnpos n hmem)]
      congr 2
      ring
    · rw [if_neg hmem, if_neg hmem]; simp
  rw [Finset.sum_congr rfl hterm]
  rw [← Finset.sum_filter]
  have hfil : (Finset.Icc (scaledN N i) (2 * scaledN N i)).filter
        (fun n => n ∈ pieceSet N i) = pieceSet N i := by
    apply Finset.Subset.antisymm
    · intro n hn; exact (Finset.mem_filter.mp hn).2
    · intro n hn; exact Finset.mem_filter.mpr ⟨hsub hn, hn⟩
  rw [hfil]

end Submission.LargeValues
