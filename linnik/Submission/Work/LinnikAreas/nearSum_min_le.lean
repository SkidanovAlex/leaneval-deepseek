import Mathlib

namespace Work.LinnikAreas

open Finset

/-- 
Bound for the truncated `min(1, ·)` sum over the integers up to `⌊2x⌋`:
the terms within distance `1` of `x` number at most two and contribute at most `1` each,
while every other term is at most `3/x` and there are at most `⌊2x⌋ ≤ 2x` of them,
giving `≤ 2 + 6 = 8 ≤ 30`. -/
theorem nearSum_min_le (x : ℝ) (hx : 1 ≤ x) :
    ∑ n ∈ Finset.Icc 1 ⌊2 * x⌋₊, min 1 (3 / (x * |x - (n:ℝ)|)) ≤ 30 := by
  have hx0 : (0:ℝ) < x := by linarith
  set N : ℕ := ⌊2 * x⌋₊ with hN
  set S : Finset ℕ := Finset.Icc 1 N with hS
  set S1 : Finset ℕ := S.filter (fun n => |(n:ℝ) - x| < 1) with hS1
  set S2 : Finset ℕ := S.filter (fun n => ¬ |(n:ℝ) - x| < 1) with hS2
  have hsplit : (∑ n ∈ S1, min 1 (3 / (x * |x - (n:ℝ)|)))
      + (∑ n ∈ S2, min 1 (3 / (x * |x - (n:ℝ)|)))
      = ∑ n ∈ S, min 1 (3 / (x * |x - (n:ℝ)|)) := by
    rw [hS1, hS2]
    exact Finset.sum_filter_add_sum_filter_not S (fun n => |(n:ℝ) - x| < 1) _
  -- the terms near `x` : there are at most two of them, each contributing at most 1
  have hsub1 : S1 ⊆ Finset.Icc ⌊x⌋₊ ⌈x⌉₊ := by
    intro n hn
    rw [hS1, Finset.mem_filter] at hn
    obtain ⟨_, hn1⟩ := hn
    rw [Finset.mem_Icc]
    have hx0' : (0:ℝ) ≤ x := le_of_lt hx0
    obtain ⟨hgt, hlt⟩ := abs_lt.mp hn1
    refine ⟨?_, ?_⟩
    · have h2 : ⌊x⌋₊ < n + 1 :=
        (Nat.floor_lt hx0').mpr (by push_cast; linarith)
      omega
    · have h2 : (n:ℝ) < ((⌈x⌉₊ + 1 : ℕ) : ℝ) := by
        push_cast
        have := Nat.le_ceil x
        linarith
      have h3 : n < ⌈x⌉₊ + 1 := by exact_mod_cast h2
      omega
  have hcard1 : S1.card ≤ 2 := by
    calc S1.card ≤ (Finset.Icc ⌊x⌋₊ ⌈x⌉₊).card := Finset.card_le_card hsub1
      _ = ⌈x⌉₊ + 1 - ⌊x⌋₊ := Nat.card_Icc _ _
      _ ≤ 2 := by
          have := Nat.ceil_le_floor_add_one x
          omega
  have hsum1 : (∑ n ∈ S1, min 1 (3 / (x * |x - (n:ℝ)|))) ≤ 2 := by
    calc (∑ n ∈ S1, min 1 (3 / (x * |x - (n:ℝ)|)))
        ≤ ∑ n ∈ S1, (1:ℝ) := Finset.sum_le_sum (fun n _ => min_le_left _ _)
      _ = (S1.card : ℝ) := by simp
      _ ≤ 2 := by
          have : (S1.card : ℝ) ≤ (2:ℝ) := by exact_mod_cast hcard1
          linarith
  -- the terms away from `x` : each contributes at most `3 / x`, and there are at most `N ≤ 2x`
  have hcard2 : S2.card ≤ N := by
    calc S2.card ≤ S.card := by rw [hS2]; exact Finset.card_filter_le _ _
      _ = N := by rw [hS]; simp
  have hsum2 : (∑ n ∈ S2, min 1 (3 / (x * |x - (n:ℝ)|))) ≤ 6 := by
    have hbound : ∀ n ∈ S2, min 1 (3 / (x * |x - (n:ℝ)|)) ≤ 3 / x := by
      intro n hn
      rw [hS2, Finset.mem_filter] at hn
      obtain ⟨_, hn2⟩ := hn
      rw [not_lt] at hn2
      have hge : 1 ≤ |x - (n:ℝ)| := by rwa [abs_sub_comm] at hn2
      calc min 1 (3 / (x * |x - (n:ℝ)|)) ≤ 3 / (x * |x - (n:ℝ)|) := min_le_right _ _
        _ ≤ 3 / x := div_le_div_of_nonneg_left (by norm_num) hx0 (by nlinarith [hge, hx0])
    calc (∑ n ∈ S2, min 1 (3 / (x * |x - (n:ℝ)|)))
        ≤ ∑ n ∈ S2, (3/x) := Finset.sum_le_sum hbound
      _ = (S2.card : ℝ) * (3/x) := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (N:ℝ) * (3/x) := by
          have h1 : (S2.card : ℝ) ≤ N := by exact_mod_cast hcard2
          have h3 : (0:ℝ) ≤ 3/x := by positivity
          nlinarith
      _ ≤ 6 := by
          have hNle : (N:ℝ) ≤ 2*x := by rw [hN]; exact Nat.floor_le (by linarith)
          have h1 : (N:ℝ) * (3/x) = 3 * (N:ℝ) / x := by ring
          rw [h1, div_le_iff₀ hx0]
          linarith
  rw [← hsplit]
  linarith

end Work.LinnikAreas
