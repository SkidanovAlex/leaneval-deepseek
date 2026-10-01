import Mathlib

/-!
# The double sum `∑_{k,l < N} h(|k-l|)`

Main result (`Work.LinnikAreas.doubleSum`): for any `h : ℕ → ℝ` and `N : ℕ`,

  `∑ k < N, ∑ l < N, (if l ≤ k then h (k - l) else h (l - k))`
    `= N * h 0 + 2 * ∑ m ∈ Icc 1 (N-1), (N - m) * h m`.

The double sum collects `h (|k - l|)` over all pairs `k, l < N`.  Splitting the
pairs into the lower triangle (`l ≤ k`) and the upper triangle (`l > k`), the
upper triangle is the mirror image of the *strict* lower triangle, so the total
is `2 * (strict lower) + (diagonal)`.  The lower triangular sum is evaluated by
the staircase identity `lowerA_formula` below, and the diagonal contributes
`N * h 0`.  Finally `lowerA_split` peels off the `m = 0` term.
-/

namespace Work.LinnikAreas

/-- One induction step for the lower triangular sum: appending a new row `k = M`
adds the sum `∑_{j < M+1} h j`. -/
lemma lowerA_step_left (h : ℕ → ℝ) (M : ℕ) :
    (∑ k ∈ Finset.range (M+1), ∑ l ∈ Finset.range (M+1), (if l ≤ k then h (k - l) else 0))
      = (∑ k ∈ Finset.range M, ∑ l ∈ Finset.range M, (if l ≤ k then h (k - l) else 0))
        + ∑ j ∈ Finset.range (M+1), h j := by
  rw [Finset.sum_range_succ]
  congr 1
  · apply Finset.sum_congr rfl; intro k hk
    rw [Finset.sum_range_succ]
    have : ¬ (M ≤ k) := by have := Finset.mem_range.mp hk; omega
    simp [this]
  · have h1 : (∑ l ∈ Finset.range (M+1), (if l ≤ M then h (M - l) else 0))
        = ∑ l ∈ Finset.range (M+1), h (M - l) := by
      apply Finset.sum_congr rfl; intro l hl
      have hl' : l ≤ M := by have := Finset.mem_range.mp hl; omega
      simp [hl']
    rw [h1]
    exact Finset.sum_range_reflect h (M+1)

/-- The same step for the closed form `∑_{d < N} (N - d) * h d`. -/
lemma lowerA_step_right (h : ℕ → ℝ) (M : ℕ) :
    (∑ d ∈ Finset.range (M+1), ((M+1:ℝ) - d) * h d)
      = (∑ d ∈ Finset.range M, ((M:ℝ) - d) * h d) + ∑ j ∈ Finset.range (M+1), h j := by
  rw [Finset.sum_range_succ (fun d => ((M+1:ℝ) - d) * h d) M, Finset.sum_range_succ h M]
  have hlast : ((M+1:ℝ) - (M:ℝ)) * h M = h M := by ring
  rw [hlast, ← add_assoc, ← Finset.sum_add_distrib]
  congr 1
  apply Finset.sum_congr rfl; intro d _
  ring

/-- Staircase identity: the lower triangular double sum equals `∑_{d < N} (N-d) h d`. -/
lemma lowerA_formula (h : ℕ → ℝ) (N : ℕ) :
    (∑ k ∈ Finset.range N, ∑ l ∈ Finset.range N, (if l ≤ k then h (k - l) else 0))
      = ∑ d ∈ Finset.range N, ((N : ℝ) - d) * h d := by
  induction N with
  | zero => simp
  | succ M ih =>
    rw [lowerA_step_left h M, ih]
    simp only [Nat.cast_add, Nat.cast_one]
    exact (lowerA_step_right h M).symm

/-- Peeling the `d = 0` term off `∑_{d < N} (N - d) h d`. -/
lemma lowerA_split (h : ℕ → ℝ) (N : ℕ) :
    (∑ d ∈ Finset.range N, ((N:ℝ) - d) * h d)
      = (N:ℝ) * h 0 + ∑ m ∈ Finset.Icc 1 (N-1), ((N:ℝ) - m) * h m := by
  rcases N with _ | M
  · simp
  · rw [Finset.sum_range_succ']
    simp only [Nat.add_sub_cancel, Nat.cast_zero, sub_zero]
    have hIco : Finset.Ico 1 (M+1) = Finset.Icc 1 M := by
      ext m; simp only [Finset.mem_Ico, Finset.mem_Icc]; omega
    have h1 : (∑ m ∈ Finset.Icc 1 M, (((M+1:ℕ):ℝ) - ↑m) * h m)
        = ∑ k ∈ Finset.range M, (((M+1:ℕ):ℝ) - ↑(k+1)) * h (k+1) := by
      rw [← hIco, Finset.sum_Ico_eq_sum_range]
      apply Finset.sum_congr rfl; intro k _
      rw [Nat.add_comm 1]
    rw [h1, add_comm]

/-- Splitting the summand according to `l ≤ k`. -/
lemma sum_split (h : ℕ → ℝ) (N : ℕ) :
    (∑ k ∈ Finset.range N, ∑ l ∈ Finset.range N, (if l ≤ k then h (k - l) else h (l - k)))
      = (∑ k ∈ Finset.range N, ∑ l ∈ Finset.range N, (if l ≤ k then h (k - l) else 0))
        + (∑ k ∈ Finset.range N, ∑ l ∈ Finset.range N, (if l ≤ k then 0 else h (l - k))) := by
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro k _
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro l _
  by_cases hc : l ≤ k <;> simp [hc]

/-- The upper triangular sum is the mirror image of the strict lower triangular sum. -/
lemma sum_B_eq_L (h : ℕ → ℝ) (N : ℕ) :
    (∑ k ∈ Finset.range N, ∑ l ∈ Finset.range N, (if l ≤ k then 0 else h (l - k)))
      = ∑ k ∈ Finset.range N, ∑ l ∈ Finset.range N, (if l < k then h (k - l) else 0) := by
  have h1 : (∑ k ∈ Finset.range N, ∑ l ∈ Finset.range N, (if l ≤ k then 0 else h (l - k)))
      = ∑ k ∈ Finset.range N, ∑ l ∈ Finset.range N, (if k < l then h (l - k) else 0) := by
    apply Finset.sum_congr rfl; intro k _
    apply Finset.sum_congr rfl; intro l _
    by_cases hc : l ≤ k
    · simp [hc, Nat.not_lt.mpr hc]
    · have hlt : k < l := Nat.lt_of_not_le hc
      simp [hc, hlt]
  rw [h1, Finset.sum_comm]

/-- Splitting the lower triangular sum into its strict part and its diagonal. -/
lemma sum_A_eq_L_add_diag (h : ℕ → ℝ) (N : ℕ) :
    (∑ k ∈ Finset.range N, ∑ l ∈ Finset.range N, (if l ≤ k then h (k - l) else 0))
      = (∑ k ∈ Finset.range N, ∑ l ∈ Finset.range N, (if l < k then h (k - l) else 0))
        + (∑ k ∈ Finset.range N, ∑ l ∈ Finset.range N, (if l = k then h 0 else 0)) := by
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro k _
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro l _
  by_cases h1 : l < k
  · have h2 : l ≤ k := le_of_lt h1
    have h3 : l ≠ k := ne_of_lt h1
    simp [h1, h2, h3]
  · by_cases h2 : l = k
    · simp [h2]
    · have h3 : ¬ (l ≤ k) := by omega
      simp [h1, h2, h3]

/-- The diagonal of the double sum contributes `N * h 0`. -/
lemma sum_diag (h : ℕ → ℝ) (N : ℕ) :
    (∑ k ∈ Finset.range N, ∑ l ∈ Finset.range N, (if l = k then h 0 else 0)) = (N:ℝ) * h 0 := by
  have hinner : ∀ k ∈ Finset.range N,
      (∑ l ∈ Finset.range N, (if l = k then h 0 else 0)) = h 0 := by
    intro k hk
    rw [Finset.sum_ite_eq']
    simp [hk]
  rw [Finset.sum_congr rfl hinner]
  simp [Finset.sum_const, Finset.card_range, nsmul_eq_mul]

/-- Counting `h (|k - l|)` over all pairs `k, l < N`. -/
theorem doubleSum (h : ℕ → ℝ) (N : ℕ) :
    (∑ k ∈ Finset.range N, ∑ l ∈ Finset.range N, (if l ≤ k then h (k - l) else h (l - k)))
      = (N : ℝ) * h 0 + 2 * ∑ m ∈ Finset.Icc 1 (N - 1), ((N : ℝ) - m) * h m := by
  have h1 := sum_split h N
  have h2 := sum_B_eq_L h N
  have h3 := sum_A_eq_L_add_diag h N
  have h4 := sum_diag h N
  have h5 := lowerA_formula h N
  have h6 := lowerA_split h N
  calc
    (∑ k ∈ Finset.range N, ∑ l ∈ Finset.range N, (if l ≤ k then h (k - l) else h (l - k)))
        = (∑ k ∈ Finset.range N, ∑ l ∈ Finset.range N, (if l ≤ k then h (k - l) else 0))
          + (∑ k ∈ Finset.range N, ∑ l ∈ Finset.range N, (if l ≤ k then 0 else h (l - k))) := h1
    _ = 2 * (∑ k ∈ Finset.range N, ∑ l ∈ Finset.range N, (if l ≤ k then h (k - l) else 0))
          - (∑ k ∈ Finset.range N, ∑ l ∈ Finset.range N, (if l = k then h 0 else 0)) := by
        rw [h2, h3]; ring
    _ = 2 * (∑ d ∈ Finset.range N, ((N:ℝ) - d) * h d) - (N:ℝ) * h 0 := by rw [h5, h4]
    _ = (N:ℝ) * h 0 + 2 * ∑ m ∈ Finset.Icc 1 (N-1), ((N:ℝ) - m) * h m := by rw [h6]; ring

end Work.LinnikAreas
