import Mathlib
import Submission.Work.HP.Q44Main.q44_sum_reindex
import Submission.Work.HP.Q44Main.q44_S1_bound
import Submission.Work.HP.Q44Main.q44_S2_bound
import Submission.Work.HP.Q44Main.q44_final_log_bound

/-!
# `q44S_window_arith_b`

For `Kmink ≥ 1` there is `K > 0` with, for every `Δ ≥ 1`,

`∑_{k ∈ {0,…,N}³, k⁰ ≤ k¹ ≤ k², k⁰+k¹+k² ≤ N}
   (2 ^ (4 k⁰ + 2 k¹ + 2 k²) + 2 ^ (k⁰ + k¹ + 3 k²)) ≤ K Δ³ (log (2Δ))²`,

where `N = ⌈logb 2 (8 Kmink (Δ+1))⌉₊`.

The sum is reindexed to a triple sum over `{0,…,N}³`
(`q44_sum_reindex`) and split into the two exponents (`q44_S1_bound`, `q44_S2_bound`),
each bounded by `2 (N+1)² 2^(3N)`: for a monotone triple the exponent is at most
`2N + 2k⁰ ≤ 3N` (resp. `N + 2k² ≤ 3N`), the inner two indices carry only `(N+1)²`
choices and the outer index contributes a geometric series handled by the constraint
`3 k⁰ ≤ N` (resp. `k² ≤ N`).  Finally `q44_final_log_bound` bounds `4(N+1)² 2^(3N)`
by `K Δ³ (log (2Δ))²`.
-/

set_option linter.unnecessarySeqFocus false

namespace Work.HP.Q44Main

/-- For `k : Fin 3 → ℕ`, monotonicity is equivalent to the two adjacent comparisons. -/
theorem monotone_fin3_iff (k : Fin 3 → ℕ) : Monotone k ↔ k 0 ≤ k 1 ∧ k 1 ≤ k 2 := by
  constructor
  · intro h; exact ⟨h (by decide), h (by decide)⟩
  · intro h i j hij
    fin_cases i <;> fin_cases j <;> simp_all <;> omega

theorem q44S_window_arith_b (Kmink : ℝ) (hKmink : 1 ≤ Kmink) :
    ∃ K : ℝ, 0 < K ∧ ∀ Δ : ℝ, 1 ≤ Δ →
      (∑ k ∈ Fintype.piFinset (fun _ : Fin 3 => Finset.range (⌈Real.logb 2 (8 * Kmink * (Δ + 1))⌉₊ + 1)),
        (if Monotone k ∧ (∑ j : Fin 3, k j) ≤ ⌈Real.logb 2 (8 * Kmink * (Δ + 1))⌉₊
          then (2 : ℝ) ^ (4 * k 0 + 2 * k 1 + 2 * k 2) + (2 : ℝ) ^ (k 0 + k 1 + 3 * k 2) else 0))
        ≤ K * Δ ^ 3 * (Real.log (2 * Δ)) ^ 2 := by
  obtain ⟨K, hKpos, hK⟩ := q44_final_log_bound Kmink hKmink
  refine ⟨K, hKpos, ?_⟩
  intro Δ hΔ
  set N : ℕ := ⌈Real.logb 2 (8 * Kmink * (Δ + 1))⌉₊ with hN
  set S1 : ℝ := ∑ a ∈ Finset.range (N + 1), ∑ b ∈ Finset.range (N + 1), ∑ c ∈ Finset.range (N + 1),
      (if a ≤ b ∧ b ≤ c ∧ a + b + c ≤ N then (2 : ℝ) ^ (4 * a + 2 * b + 2 * c) else 0) with hS1
  set S2 : ℝ := ∑ a ∈ Finset.range (N + 1), ∑ b ∈ Finset.range (N + 1), ∑ c ∈ Finset.range (N + 1),
      (if a ≤ b ∧ b ≤ c ∧ a + b + c ≤ N then (2 : ℝ) ^ (a + b + 3 * c) else 0) with hS2
  -- rewrite the summand as a function of the three coordinates
  have hcongr : ∀ k : Fin 3 → ℕ,
      (if Monotone k ∧ (∑ j : Fin 3, k j) ≤ N
        then (2 : ℝ) ^ (4 * k 0 + 2 * k 1 + 2 * k 2) + (2 : ℝ) ^ (k 0 + k 1 + 3 * k 2) else 0)
      = (if k 0 ≤ k 1 ∧ k 1 ≤ k 2 ∧ k 0 + k 1 + k 2 ≤ N
        then (2 : ℝ) ^ (4 * k 0 + 2 * k 1 + 2 * k 2) + (2 : ℝ) ^ (k 0 + k 1 + 3 * k 2) else 0) := by
    intro k
    have hcond : (Monotone k ∧ (∑ j : Fin 3, k j) ≤ N)
        ↔ (k 0 ≤ k 1 ∧ k 1 ≤ k 2 ∧ k 0 + k 1 + k 2 ≤ N) := by
      rw [monotone_fin3_iff k, Fin.sum_univ_three]; simp only [and_assoc]
    exact if_congr hcond rfl rfl
  have hreindex : (∑ k ∈ Fintype.piFinset (fun _ : Fin 3 => Finset.range (N + 1)),
        (if Monotone k ∧ (∑ j : Fin 3, k j) ≤ N
          then (2 : ℝ) ^ (4 * k 0 + 2 * k 1 + 2 * k 2) + (2 : ℝ) ^ (k 0 + k 1 + 3 * k 2) else 0))
      = ∑ a ∈ Finset.range (N + 1), ∑ b ∈ Finset.range (N + 1), ∑ c ∈ Finset.range (N + 1),
        (if a ≤ b ∧ b ≤ c ∧ a + b + c ≤ N
          then (2 : ℝ) ^ (4 * a + 2 * b + 2 * c) + (2 : ℝ) ^ (a + b + 3 * c) else 0) := by
    rw [Finset.sum_congr rfl
      (fun k (_ : k ∈ Fintype.piFinset (fun _ : Fin 3 => Finset.range (N + 1))) =>
        hcongr k)]
    exact q44_sum_reindex N (fun a b c => if a ≤ b ∧ b ≤ c ∧ a + b + c ≤ N
          then (2 : ℝ) ^ (4 * a + 2 * b + 2 * c) + (2 : ℝ) ^ (a + b + 3 * c) else 0)
  -- split the conditional sum of the two exponents
  have hsplit : (∑ a ∈ Finset.range (N + 1), ∑ b ∈ Finset.range (N + 1), ∑ c ∈ Finset.range (N + 1),
        (if a ≤ b ∧ b ≤ c ∧ a + b + c ≤ N
          then (2 : ℝ) ^ (4 * a + 2 * b + 2 * c) + (2 : ℝ) ^ (a + b + 3 * c) else 0))
      = S1 + S2 := by
    rw [hS1, hS2]
    calc (∑ a ∈ Finset.range (N + 1), ∑ b ∈ Finset.range (N + 1), ∑ c ∈ Finset.range (N + 1),
        (if a ≤ b ∧ b ≤ c ∧ a + b + c ≤ N
          then (2 : ℝ) ^ (4 * a + 2 * b + 2 * c) + (2 : ℝ) ^ (a + b + 3 * c) else 0))
        = ∑ a ∈ Finset.range (N + 1), ∑ b ∈ Finset.range (N + 1), ∑ c ∈ Finset.range (N + 1),
            ((if a ≤ b ∧ b ≤ c ∧ a + b + c ≤ N then (2 : ℝ) ^ (4 * a + 2 * b + 2 * c) else 0)
            + (if a ≤ b ∧ b ≤ c ∧ a + b + c ≤ N then (2 : ℝ) ^ (a + b + 3 * c) else 0)) := by
          apply Finset.sum_congr rfl; intro a _
          apply Finset.sum_congr rfl; intro b _
          apply Finset.sum_congr rfl; intro c _
          by_cases h : a ≤ b ∧ b ≤ c ∧ a + b + c ≤ N <;> simp [h]
      _ = _ := by simp only [Finset.sum_add_distrib]
  have hs1 : S1 ≤ 2 * ((N : ℝ) + 1) ^ 2 * (2 : ℝ) ^ (3 * N) := by rw [hS1]; exact q44_S1_bound N
  have hs2 : S2 ≤ 2 * ((N : ℝ) + 1) ^ 2 * (2 : ℝ) ^ (3 * N) := by rw [hS2]; exact q44_S2_bound N
  have hfin : 4 * ((N : ℝ) + 1) ^ 2 * (2 : ℝ) ^ (3 * N) ≤ K * Δ ^ 3 * (Real.log (2 * Δ)) ^ 2 := by
    have h := hK Δ hΔ
    rw [← hN] at h
    exact h
  calc (∑ k ∈ Fintype.piFinset (fun _ : Fin 3 => Finset.range (N + 1)),
        (if Monotone k ∧ (∑ j : Fin 3, k j) ≤ N
          then (2 : ℝ) ^ (4 * k 0 + 2 * k 1 + 2 * k 2) + (2 : ℝ) ^ (k 0 + k 1 + 3 * k 2) else 0))
      = S1 + S2 := by rw [hreindex, hsplit]
    _ ≤ 2 * ((N : ℝ) + 1) ^ 2 * (2 : ℝ) ^ (3 * N)
        + 2 * ((N : ℝ) + 1) ^ 2 * (2 : ℝ) ^ (3 * N) := add_le_add hs1 hs2
    _ = 4 * ((N : ℝ) + 1) ^ 2 * (2 : ℝ) ^ (3 * N) := by ring
    _ ≤ K * Δ ^ 3 * (Real.log (2 * Δ)) ^ 2 := hfin

end Work.HP.Q44Main
