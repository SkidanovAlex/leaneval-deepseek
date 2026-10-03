import Mathlib

/-!
# A logarithmic bound for the two-dimensional lattice sum `∑_{a,b ≤ N} 1/(a² + b²)`

We prove that the double sum `∑_{a=0}^{N} ∑_{b=0}^{N} 1/(a² + b²)` grows at most
like `log N`.  The proof is an induction on `N`: passing from `N` to `N+1` adds
one new row `(a, N+1)`, `0 ≤ a ≤ N`, and one new column `(N+1, b)`, `0 ≤ b ≤ N+1`.
On the row every term is at most `1/(N+1)²`, so the row contributes at most
`(N+1)/(N+1)² = 1/(N+1)`; on the column every term is also at most `1/(N+1)²`,
so it contributes at most `(N+2)/(N+1)² ≤ 2/(N+1)`.  Hence the increment at step
`N+1` is at most `3/(N+1)`, and summing gives `≤ 3 H_N ≤ 3 (1 + log N)`.
-/

namespace Work.FIArea7

/-- The double sum `∑_{a,b ≤ N} 1/(a² + b²)`, written over `range (N+1)`. -/
private noncomputable def L2 (N : ℕ) : ℝ :=
  ∑ a ∈ Finset.range (N + 1), ∑ b ∈ Finset.range (N + 1),
    (1 : ℝ) / ((a : ℝ) ^ 2 + (b : ℝ) ^ 2)

/-- The `N`-th harmonic number, as a real. -/
private def Hh (N : ℕ) : ℝ := ((harmonic N : ℚ) : ℝ)

private lemma Hh_succ (N : ℕ) : Hh (N + 1) = Hh N + 1 / ((N + 1 : ℕ) : ℝ) := by
  unfold Hh
  rw [harmonic_succ, Rat.cast_add, Rat.cast_inv, Rat.cast_natCast, one_div]

/-- Splitting off the new row and column when passing from `N` to `N+1`. -/
private lemma L2_succ_decomp (N : ℕ) :
    L2 (N + 1) = L2 N
      + (∑ a ∈ Finset.range (N + 1), (1 : ℝ) / ((a : ℝ) ^ 2 + ((N + 1 : ℕ) : ℝ) ^ 2))
      + (∑ b ∈ Finset.range (N + 2), (1 : ℝ) / (((N + 1 : ℕ) : ℝ) ^ 2 + (b : ℝ) ^ 2)) := by
  unfold L2
  simp only [Finset.sum_range_succ, Finset.sum_add_distrib]
  ring

/-- The new row contributes at most `1/(N+1)`. -/
private lemma row_le (N : ℕ) :
    (∑ a ∈ Finset.range (N + 1), (1 : ℝ) / ((a : ℝ) ^ 2 + ((N + 1 : ℕ) : ℝ) ^ 2))
      ≤ 1 / ((N + 1 : ℕ) : ℝ) := by
  have hx : (0 : ℝ) < ((N + 1 : ℕ) : ℝ) := by positivity
  calc ∑ a ∈ Finset.range (N + 1), (1 : ℝ) / ((a : ℝ) ^ 2 + ((N + 1 : ℕ) : ℝ) ^ 2)
      ≤ ∑ a ∈ Finset.range (N + 1), (1 : ℝ) / (((N + 1 : ℕ) : ℝ) ^ 2) := by
        apply Finset.sum_le_sum; intro a ha
        apply one_div_le_one_div_of_le (pow_pos hx 2)
        nlinarith [sq_nonneg (a : ℝ)]
    _ = ((N + 1 : ℕ) : ℝ) * (1 / (((N + 1 : ℕ) : ℝ) ^ 2)) := by
        rw [Finset.sum_const, Finset.card_range]; simp
    _ = 1 / ((N + 1 : ℕ) : ℝ) := by field_simp

/-- The new column contributes at most `(N+2)/(N+1)²`. -/
private lemma col_le (N : ℕ) :
    (∑ b ∈ Finset.range (N + 2), (1 : ℝ) / (((N + 1 : ℕ) : ℝ) ^ 2 + (b : ℝ) ^ 2))
      ≤ ((N + 2 : ℕ) : ℝ) / (((N + 1 : ℕ) : ℝ) ^ 2) := by
  have hx : (0 : ℝ) < ((N + 1 : ℕ) : ℝ) := by positivity
  calc ∑ b ∈ Finset.range (N + 2), (1 : ℝ) / (((N + 1 : ℕ) : ℝ) ^ 2 + (b : ℝ) ^ 2)
      ≤ ∑ b ∈ Finset.range (N + 2), (1 : ℝ) / (((N + 1 : ℕ) : ℝ) ^ 2) := by
        apply Finset.sum_le_sum; intro b hb
        apply one_div_le_one_div_of_le (pow_pos hx 2)
        nlinarith [sq_nonneg (b : ℝ)]
    _ = ((N + 2 : ℕ) : ℝ) * (1 / (((N + 1 : ℕ) : ℝ) ^ 2)) := by
        rw [Finset.sum_const, Finset.card_range]; simp
    _ = ((N + 2 : ℕ) : ℝ) / (((N + 1 : ℕ) : ℝ) ^ 2) := by ring

/-- One step of the induction: the increment is at most `3/(N+1)`. -/
private lemma L2_step (N : ℕ) : L2 (N + 1) ≤ L2 N + 3 / ((N + 1 : ℕ) : ℝ) := by
  have hx : (0 : ℝ) < ((N + 1 : ℕ) : ℝ) := by positivity
  rw [L2_succ_decomp N]
  have h1 := row_le N
  have h2 := col_le N
  have h3 : ((N + 2 : ℕ) : ℝ) / ((N + 1 : ℕ) : ℝ) ^ 2 ≤ 2 / ((N + 1 : ℕ) : ℝ) := by
    rw [div_le_div_iff₀ (pow_pos hx 2) hx]
    have h4 : ((N + 2 : ℕ) : ℝ) ≤ 2 * ((N + 1 : ℕ) : ℝ) := by push_cast; linarith
    nlinarith [hx]
  have h2' : (∑ b ∈ Finset.range (N + 2), (1 : ℝ) / (((N + 1 : ℕ) : ℝ) ^ 2 + (b : ℝ) ^ 2))
      ≤ 2 / ((N + 1 : ℕ) : ℝ) := le_trans h2 h3
  have hsum : (∑ a ∈ Finset.range (N + 1), (1 : ℝ) / ((a : ℝ) ^ 2 + ((N + 1 : ℕ) : ℝ) ^ 2))
      + (∑ b ∈ Finset.range (N + 2), (1 : ℝ) / (((N + 1 : ℕ) : ℝ) ^ 2 + (b : ℝ) ^ 2))
      ≤ 3 / ((N + 1 : ℕ) : ℝ) := by
    calc _ ≤ 1 / ((N + 1 : ℕ) : ℝ) + 2 / ((N + 1 : ℕ) : ℝ) := add_le_add h1 h2'
      _ = 3 / ((N + 1 : ℕ) : ℝ) := by ring
  linarith

/-- `L2 N ≤ 3 H_N`. -/
private lemma L2_le (N : ℕ) : L2 N ≤ 3 * Hh N := by
  induction N with
  | zero =>
      have hL : L2 0 = 0 := by unfold L2; norm_num
      simp [hL, Hh, harmonic_zero]
  | succ N ih =>
      have h := L2_step N
      have hs := Hh_succ N
      calc L2 (N + 1) ≤ L2 N + 3 / ((N + 1 : ℕ) : ℝ) := h
        _ ≤ 3 * Hh N + 3 / ((N + 1 : ℕ) : ℝ) := by linarith
        _ = 3 * Hh (N + 1) := by rw [hs]; ring

/-- Monotonicity of the harmonic numbers. -/
private lemma Hh_le_two (N : ℕ) : Hh N ≤ Hh (N + 2) := by
  unfold Hh
  rw [harmonic_eq_sum_Icc (n := N), harmonic_eq_sum_Icc (n := N + 2), Rat.cast_sum, Rat.cast_sum]
  simp only [Rat.cast_inv, Rat.cast_natCast]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.Icc_subset_Icc_right (by omega))
    (fun i _ _ => by positivity)

/-- **Two-dimensional lattice sum bound.** The sum of `1/(a²+b²)` over the square
`0 ≤ a, b ≤ N` is `O(log N)`. -/
theorem lattice_sum_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ,
      (∑ a ∈ Finset.Icc 0 N, ∑ b ∈ Finset.Icc 0 N,
        (1 : ℝ) / ((a : ℝ) ^ 2 + (b : ℝ) ^ 2))
        ≤ C * (1 + Real.log (2 + (N : ℝ))) := by
  refine ⟨3, by norm_num, fun N => ?_⟩
  have hIcc : Finset.Icc 0 N = Finset.range (N + 1) := by
    ext k; simp [Finset.mem_Icc, Finset.mem_range]
  rw [hIcc]
  change L2 N ≤ 3 * (1 + Real.log (2 + (N : ℝ)))
  have hlog := harmonic_le_one_add_log (N + 2)
  have hcast : ((N + 2 : ℕ) : ℝ) = 2 + (N : ℝ) := by push_cast; ring
  rw [hcast] at hlog
  calc L2 N ≤ 3 * Hh N := L2_le N
    _ ≤ 3 * Hh (N + 2) := mul_le_mul_of_nonneg_left (Hh_le_two N) (by norm_num)
    _ ≤ 3 * (1 + Real.log (2 + (N : ℝ))) := mul_le_mul_of_nonneg_left hlog (by norm_num)

end Work.FIArea7
