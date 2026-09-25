import Mathlib

namespace Commons.Analysis.ExponentialSums

open Finset
open scoped BigOperators

theorem min_le_one_add_card_div (M : ℕ) (hM : 1 ≤ M) {D : ℝ} (hD : 0 < D) :
    min (M:ℝ) ((1/2)/D)
      ≤ 1 + ((Finset.filter (fun k : ℕ => D ≤ 1/(2*(k:ℝ))) (Finset.Icc 1 M)).card : ℝ) := by
  set a : ℝ := 1/(2*D) with ha
  have haeq : (1/2)/D = a := by rw [ha, div_div]
  rw [haeq]
  set S := Finset.filter (fun k : ℕ => D ≤ 1/(2*(k:ℝ))) (Finset.Icc 1 M) with hS
  have hcnt : ((min M ⌊a⌋₊ : ℕ) : ℝ) ≤ (S.card : ℝ) := by
    have hsub : Finset.Icc 1 (min M ⌊a⌋₊) ⊆ S := by
      intro s hs
      rw [hS, Finset.mem_filter, Finset.mem_Icc]
      rw [Finset.mem_Icc] at hs
      refine ⟨⟨hs.1, le_trans hs.2 (min_le_left _ _)⟩, ?_⟩
      have hs0 : (0:ℝ) < (s:ℝ) := by exact_mod_cast (by omega : 0 < s)
      have hsle : (s:ℝ) ≤ a := by
        have h1 : s ≤ ⌊a⌋₊ := le_trans hs.2 (min_le_right _ _)
        have h2 : (s:ℝ) ≤ (⌊a⌋₊ : ℝ) := by exact_mod_cast h1
        exact le_trans h2 (Nat.floor_le (by rw [ha]; positivity))
      rw [ha] at hsle
      rw [le_div_iff₀ (by positivity : (0:ℝ) < 2*D)] at hsle
      rw [le_div_iff₀ (by positivity : (0:ℝ) < 2*(s:ℝ))]
      nlinarith [hsle]
    calc ((min M ⌊a⌋₊ : ℕ) : ℝ) = ((Finset.Icc 1 (min M ⌊a⌋₊)).card : ℝ) := by
          rw [Nat.card_Icc]; push_cast; ring
      _ ≤ (S.card : ℝ) := by exact_mod_cast Finset.card_le_card hsub
  have hminle : min (M:ℝ) a ≤ ((min M ⌊a⌋₊ : ℕ) : ℝ) + 1 := by
    rw [Nat.cast_min]
    rcases le_or_gt (M:ℝ) ((⌊a⌋₊ : ℕ) : ℝ) with h | h
    · rw [min_eq_left h]
      have : min (M:ℝ) a ≤ M := min_le_left _ _
      linarith
    · rw [min_eq_right (le_of_lt h)]
      have ha2 : a < ((⌊a⌋₊ : ℕ) : ℝ) + 1 := Nat.lt_floor_add_one a
      have : min (M:ℝ) a ≤ a := min_le_right _ _
      linarith
  have hM1 : (1:ℝ) ≤ (M:ℝ) := by exact_mod_cast hM
  linarith [hminle, hcnt, hM1]

end Commons.Analysis.ExponentialSums
