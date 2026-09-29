import Mathlib
import Submission.Work.TMC16Core.Core.nr_ladder

namespace Work.TMC16Core.Main

/-- For a positive integer `d` and any integer `y`, there is a quotient `m` and a
centered residue `k₀ ∈ [0, d/2]` that is congruent to `±y` modulo `d`: either
`k₀ = y - m d` (the ordinary remainder) or `k₀ = (m+1) d - y` (its complement). -/
lemma centered_residue {d y : ℤ} (hd : 0 < d) :
    ∃ m k₀ : ℤ, m * d ≤ y ∧ y < (m + 1) * d ∧ 0 ≤ k₀ ∧ k₀ ≤ d / 2 ∧
      (k₀ = y - m * d ∨ k₀ = (m + 1) * d - y) := by
  have hdne : d ≠ 0 := ne_of_gt hd
  have hr0 : 0 ≤ y % d := Int.emod_nonneg y hdne
  have hrd : y % d < d := Int.emod_lt_of_pos y hd
  have hy : y / d * d + y % d = y := Int.ediv_mul_add_emod y d
  refine ⟨y / d, min (y % d) (d - y % d), ?_, ?_, ?_, ?_, ?_⟩
  · linarith
  · have hh : (y / d + 1) * d = y / d * d + d := by ring
    rw [hh]; linarith
  · exact le_min hr0 (by linarith)
  · rw [Int.le_ediv_iff_mul_le (by norm_num : (0:ℤ) < 2)]
    have h1 : min (y % d) (d - y % d) ≤ y % d := min_le_left _ _
    have h2 : min (y % d) (d - y % d) ≤ d - y % d := min_le_right _ _
    linarith
  · rcases le_total (y % d) (d - y % d) with h | h
    · left
      rw [min_eq_left h]; linarith
    · right
      rw [min_eq_right h]
      have hh : (y / d + 1) * d = y / d * d + d := by ring
      linarith

theorem level_data {q : ℕ → ℕ} (hqpos : ∀ i, 0 < q i) (hmono : StrictMono q) :
    ∃ Y : ℝ, ∀ y : ℤ, Y ≤ (y : ℝ) → ∃ n : ℕ, ∃ m k₀ : ℤ, ∃ s : ℕ,
      3 ≤ n ∧ 1 ≤ y ∧
      max (Real.rpow (q n : ℝ) (8 / 9)) ((q (n - 1) : ℝ) / 20) < (y : ℝ) ∧
      (y : ℝ) ≤ max (Real.rpow (q (n + 1) : ℝ) (8 / 9)) ((q n : ℝ) / 20) ∧
      m * (q n : ℤ) ≤ y ∧ y < (m + 1) * (q n : ℤ) ∧
      0 ≤ k₀ ∧ k₀ ≤ (q n : ℤ) / 2 ∧
      (k₀ = y - m * (q n : ℤ) ∨ k₀ = (m + 1) * (q n : ℤ) - y) ∧
      s = k₀.toNat / q (n - 1) := by
  obtain ⟨Y₀, hY₀⟩ := Work.TMC16Core.Core.nr_ladder hqpos hmono
  refine ⟨max Y₀ 1, ?_⟩
  intro y hy
  have hy0 : Y₀ ≤ (y : ℝ) := le_trans (le_max_left _ _) hy
  have hy1 : (1 : ℝ) ≤ (y : ℝ) := le_trans (le_max_right _ _) hy
  have hy1' : (1 : ℤ) ≤ y := by exact_mod_cast hy1
  obtain ⟨n, hn3, hlow, hup⟩ := hY₀ y hy0
  have hd : 0 < (q n : ℤ) := by exact_mod_cast hqpos n
  obtain ⟨m, k₀, hm1, hm2, hk0a, hk0b, hkdisj⟩ := centered_residue hd
  exact ⟨n, m, k₀, k₀.toNat / q (n - 1), hn3, hy1', hlow, hup,
    hm1, hm2, hk0a, hk0b, hkdisj, rfl⟩

end Work.TMC16Core.Main
