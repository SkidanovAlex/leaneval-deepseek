import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF.SD

open Finset

/-- Abel summation (the `sum_range_by_parts'` identity) combined with the geometric
bound `‖Σ_{j<n} ζ^j‖ ≤ min n (2/‖ζ-1‖)` for `‖ζ‖ = 1`, `ζ ≠ 1`, gives a bound for
`Σ_{m<M} ζ^m w m` in terms of the total variation `ε` of `w` on `[0,M)` and its
sup-norm (`≤ 1`). -/
theorem abel_geom_bound (ζ : ℂ) (w : ℕ → ℂ) (M : ℕ) (ε : ℝ)
    (hζ : ‖ζ‖ = 1) (hζ1 : ζ ≠ 1)
    (hw : ∀ m < M, ‖w (m+1) - w m‖ ≤ ε)
    (hw1 : ∀ m < M, ‖w m‖ ≤ 1) :
    ‖∑ m ∈ Finset.range M, ζ ^ m * w m‖ ≤ (1 + (M:ℝ) * ε) * min (M:ℝ) (2 / ‖ζ - 1‖) := by
  rcases Nat.eq_zero_or_pos M with hM0 | hM
  · subst hM0
    simp only [Finset.sum_range_zero, norm_zero, Nat.cast_zero, zero_mul, add_zero, one_mul]
    exact le_min le_rfl (div_nonneg (by norm_num : (0:ℝ) ≤ 2) (norm_nonneg (ζ - 1)))
  have hε : 0 ≤ ε := le_trans (norm_nonneg _) (hw 0 hM)
  have hden : 0 < ‖ζ - 1‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hζ1)
  have hmin0 : 0 ≤ min (M:ℝ) (2/‖ζ-1‖) :=
    le_min (Nat.cast_nonneg M) (le_of_lt (div_pos (by norm_num) hden))
  -- partial geometric sums of `ζ` are bounded by `2 / ‖ζ - 1‖`
  have hgeom2 : ∀ n, ‖∑ j ∈ Finset.range n, ζ ^ j‖ ≤ 2/‖ζ-1‖ := by
    intro n
    rw [geom_sum_eq hζ1 n, norm_div]
    apply div_le_div_of_nonneg_right _ (norm_nonneg _)
    calc ‖ζ ^ n - 1‖ ≤ ‖ζ ^ n‖ + ‖1‖ := norm_sub_le _ _
      _ = 2 := by rw [norm_pow, hζ, one_pow, norm_one]; norm_num
  -- ... and also by the number of terms, hence by `M`
  have hgeomM : ∀ n, n ≤ M → ‖∑ j ∈ Finset.range n, ζ ^ j‖ ≤ (M:ℝ) := by
    intro n hn
    calc ‖∑ j ∈ Finset.range n, ζ ^ j‖ ≤ ∑ j ∈ Finset.range n, ‖ζ ^ j‖ := norm_sum_le _ _
      _ = ∑ j ∈ Finset.range n, (1:ℝ) := by
            apply Finset.sum_congr rfl; intro j _; rw [norm_pow, hζ, one_pow]
      _ = (n:ℝ) := by simp
      _ ≤ (M:ℝ) := by exact_mod_cast hn
  have hG : ∀ n, n ≤ M → ‖∑ j ∈ Finset.range n, ζ ^ j‖ ≤ min (M:ℝ) (2/‖ζ-1‖) :=
    fun n hn => le_min (hgeomM n hn) (hgeom2 n)
  -- Abel summation by parts
  have habel : (∑ m ∈ Finset.range M, ζ ^ m * w m)
      = (∑ j ∈ Finset.range M, ζ^j) * w (M-1)
        - ∑ i ∈ Finset.range (M - 1), (∑ j ∈ Finset.range (i+1), ζ^j) * (w (i+1) - w i) := by
    have h := Finset.sum_range_by_parts' (f := fun i => ζ^i) (g := w) M
    simpa [smul_eq_mul] using h
  rw [habel]
  refine le_trans (norm_sub_le _ _) ?_
  have h1 : ‖(∑ j ∈ Finset.range M, ζ^j) * w (M-1)‖ ≤ min (M:ℝ) (2/‖ζ-1‖) := by
    rw [norm_mul]
    calc ‖∑ j ∈ Finset.range M, ζ^j‖ * ‖w (M-1)‖
        ≤ min (M:ℝ) (2/‖ζ-1‖) * 1 :=
          mul_le_mul (hG M le_rfl) (hw1 (M-1) (by omega)) (norm_nonneg _) hmin0
      _ = min (M:ℝ) (2/‖ζ-1‖) := by ring
  have h2 : ‖∑ i ∈ Finset.range (M - 1), (∑ j ∈ Finset.range (i+1), ζ^j) * (w (i+1) - w i)‖
      ≤ ((M-1:ℕ):ℝ) * (min (M:ℝ) (2/‖ζ-1‖) * ε) := by
    calc ‖∑ i ∈ Finset.range (M - 1), (∑ j ∈ Finset.range (i+1), ζ^j) * (w (i+1) - w i)‖
        ≤ ∑ i ∈ Finset.range (M-1),
            ‖(∑ j ∈ Finset.range (i+1), ζ^j) * (w (i+1) - w i)‖ := norm_sum_le _ _
      _ = ∑ i ∈ Finset.range (M-1),
            ‖∑ j ∈ Finset.range (i+1), ζ^j‖ * ‖w (i+1) - w i‖ := by
            apply Finset.sum_congr rfl; intro i _; rw [norm_mul]
      _ ≤ ∑ i ∈ Finset.range (M-1), min (M:ℝ) (2/‖ζ-1‖) * ε := by
            apply Finset.sum_le_sum; intro i hi
            have hiM : i + 1 ≤ M := by simp at hi; omega
            have hi' : i < M := by simp at hi; omega
            exact mul_le_mul (hG (i+1) hiM) (hw i hi') (norm_nonneg _) hmin0
      _ = ((M-1:ℕ):ℝ) * (min (M:ℝ) (2/‖ζ-1‖) * ε) := by
            rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  refine le_trans (add_le_add h1 h2) ?_
  have hMN : ((M-1:ℕ):ℝ) = (M:ℝ) - 1 := by rw [Nat.cast_sub hM, Nat.cast_one]
  have hMnn : (0:ℝ) ≤ (M:ℝ) := Nat.cast_nonneg M
  nlinarith [hMN, hmin0, hε, hMnn, mul_nonneg hmin0 hε]

end Work.BMF.SD
