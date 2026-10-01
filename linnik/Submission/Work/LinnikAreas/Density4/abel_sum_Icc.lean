import Mathlib

namespace Work.LinnikAreas.Density4

/-- Reindex a sum over `Finset.Icc 1 N` as a sum over `Finset.range N`. -/
lemma sum_range_Icc_one (h : ℕ → ℝ) (N : ℕ) :
    ∑ n ∈ Finset.Icc 1 N, h n = ∑ j ∈ Finset.range N, h (j + 1) := by
  have hIcc : Finset.Icc 1 N = Finset.Ico 1 (N + 1) := by
    ext x; simp [Finset.mem_Icc, Finset.mem_Ico]
  rw [hIcc, Finset.sum_Ico_eq_sum_range]
  rw [Nat.add_sub_cancel]
  apply Finset.sum_congr rfl
  intro j hj
  rw [Nat.add_comm 1 j]

/-- Abel summation in the `Finset.range` formulation. -/
lemma abel_sum_range (b g : ℕ → ℝ) (N : ℕ) :
    ∑ n ∈ Finset.range N, b n * g n
      = (∑ n ∈ Finset.range N, b n) * g (N - 1)
        + ∑ n ∈ Finset.range (N - 1),
            (∑ k ∈ Finset.range (n + 1), b k) * (g n - g (n + 1)) := by
  have h := Finset.sum_range_by_parts (f := g) (g := b) N
  simp only [smul_eq_mul] at h
  rw [show (∑ n ∈ Finset.range N, b n * g n) = ∑ n ∈ Finset.range N, g n * b n from
        Finset.sum_congr rfl (fun n _ => mul_comm (b n) (g n))]
  rw [h, mul_comm (g (N - 1)) (∑ n ∈ Finset.range N, b n), sub_eq_add_neg,
    add_left_cancel_iff]
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro n _
  ring

/-- Abel summation (partial summation) for sums over `Finset.Icc 1 N`. -/
theorem abel_sum_Icc (a f : ℕ → ℝ) (N : ℕ) :
    ∑ n ∈ Finset.Icc 1 N, a n * f n
      = (∑ n ∈ Finset.Icc 1 N, a n) * f N
        + ∑ n ∈ Finset.Icc 1 (N - 1), (∑ k ∈ Finset.Icc 1 n, a k) * (f n - f (n + 1)) := by
  rcases Nat.eq_zero_or_pos N with hN | hN
  · subst hN; simp
  · have hkey := abel_sum_range (fun j => a (j + 1)) (fun j => f (j + 1)) N
    have h2 : (∑ n ∈ Finset.Icc 1 N, a n) * f N
        + ∑ n ∈ Finset.Icc 1 (N - 1), (∑ k ∈ Finset.Icc 1 n, a k) * (f n - f (n + 1))
      = (∑ j ∈ Finset.range N, a (j + 1)) * f ((N - 1) + 1)
        + ∑ j ∈ Finset.range (N - 1),
            (∑ k ∈ Finset.range (j + 1), a (k + 1)) * (f (j + 1) - f ((j + 1) + 1)) := by
      rw [sum_range_Icc_one (fun n => a n) N]
      congr 1
      · rw [Nat.sub_add_cancel hN]
      · rw [sum_range_Icc_one
            (fun n => (∑ k ∈ Finset.Icc 1 n, a k) * (f n - f (n + 1))) (N - 1)]
        apply Finset.sum_congr rfl
        intro j hj
        rw [sum_range_Icc_one (fun k => a k) (j + 1)]
    rw [sum_range_Icc_one (fun n => a n * f n) N, hkey, ← h2]

end Work.LinnikAreas.Density4
