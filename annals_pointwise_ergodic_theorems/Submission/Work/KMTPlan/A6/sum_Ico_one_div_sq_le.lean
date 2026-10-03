import Mathlib

namespace Work.KMTPlan.A6

/-- Telescoping identity: for `K ≤ M`, the sum of successive differences over `Ico K M`
equals `g K - g M`. (For `K > M` the sum is empty and no such identity holds in general.) -/
private lemma sum_Ico_telescope (g : ℕ → ℝ) {K M : ℕ} (hKM : K ≤ M) :
    ∑ n ∈ Finset.Ico K M, (g n - g (n + 1)) = g K - g M := by
  rw [Finset.sum_Ico_eq_sum_range]
  have h2 : ∑ k ∈ Finset.range (M - K), (g (K + k) - g (K + k + 1))
      = g K - g (K + (M - K)) := by
    have h := Finset.sum_range_sub' (fun k => g (K + k)) (M - K)
    simpa only [Nat.add_zero, ← Nat.add_assoc] using h
  simpa only [Nat.add_sub_cancel' hKM] using h2

/-- `∑_{K ≤ n < M} 1/(n+1)^2 ≤ 1/K` for `K ≥ 1`: each term is bounded by the telescoping
difference `1/n - 1/(n+1) = 1/(n(n+1)) ≥ 1/(n+1)^2`, and the sum telescopes to
`1/K - 1/M ≤ 1/K`. -/
theorem sum_Ico_one_div_sq_le (K M : ℕ) (hK : 1 ≤ K) :
    ∑ n ∈ Finset.Ico K M, (1 : ℝ) / (((n + 1 : ℕ) : ℝ) ^ 2) ≤ 1 / (K : ℝ) := by
  have hterm : ∀ n : ℕ, K ≤ n →
      (1 : ℝ) / (((n + 1 : ℕ) : ℝ) ^ 2) ≤ 1 / (n : ℝ) - 1 / ((n + 1 : ℕ) : ℝ) := by
    intro n hn
    have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (le_trans hK hn)
    have hnpos : (0 : ℝ) < (n : ℝ) := by linarith
    have hnp1 : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by
      have : (0:ℕ) < n + 1 := Nat.succ_pos n
      exact_mod_cast this
    rw [div_sub_div _ _ (ne_of_gt hnpos) (ne_of_gt hnp1)]
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    push_cast
    nlinarith
  rcases Nat.lt_or_ge M K with hMK | hKM
  · rw [Finset.Ico_eq_empty_iff.mpr (not_lt.mpr (le_of_lt hMK))]
    simp only [Finset.sum_empty]
    positivity
  · calc ∑ n ∈ Finset.Ico K M, (1 : ℝ) / (((n + 1 : ℕ) : ℝ) ^ 2)
        ≤ ∑ n ∈ Finset.Ico K M, (1 / (n : ℝ) - 1 / ((n + 1 : ℕ) : ℝ)) :=
          Finset.sum_le_sum (fun n hn => hterm n (Finset.mem_Ico.mp hn).1)
      _ = 1 / (K : ℝ) - 1 / (M : ℝ) := by
          simpa using sum_Ico_telescope (fun n => 1 / (n : ℝ)) hKM
      _ ≤ 1 / (K : ℝ) := by
          have hM : (0:ℝ) ≤ 1 / (M : ℝ) := by positivity
          linarith

end Work.KMTPlan.A6
