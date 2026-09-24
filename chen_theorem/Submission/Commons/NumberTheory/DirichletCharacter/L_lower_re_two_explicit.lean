import Mathlib.NumberTheory.LSeries.DirichletContinuation

set_option autoImplicit false
set_option linter.unusedVariables false

open Complex DirichletCharacter
open scoped BigOperators

namespace Commons.NumberTheory.DirichletCharacter

/-- Partial sums of the tail majorant `∑_{2 ≤ n} 1 / n²` are bounded by `3 / 4`. -/
private lemma partial_sum_guard_le (K : ℕ) :
    (∑ n ∈ Finset.range K, (if 2 ≤ n then ((n : ℝ) ^ 2)⁻¹ else 0)) ≤ 3 / 4 := by
  by_cases hK : 3 ≤ K
  · have h1 : (∑ n ∈ Finset.range K, (if 2 ≤ n then ((n : ℝ) ^ 2)⁻¹ else 0))
        = ∑ n ∈ Finset.Icc 2 (K - 1), ((n : ℝ) ^ 2)⁻¹ := by
          rw [← Finset.sum_filter (s := Finset.range K) (p := fun n : ℕ => 2 ≤ n)
            (f := fun n : ℕ => ((n : ℝ) ^ 2)⁻¹)]
          congr 1
          ext n
          simp [Finset.mem_filter, Finset.mem_range, Finset.mem_Icc]
          omega
    rw [h1]
    have hsplit := Finset.add_sum_Ioc_eq_sum_Icc (α := ℕ) (M := ℝ)
      (f := fun n : ℕ => ((n : ℝ) ^ 2)⁻¹) (a := 2) (b := K - 1) (by omega : 2 ≤ K - 1)
    rw [← hsplit]
    have hS : (∑ i ∈ Finset.Ioc 2 (K - 1), ((i : ℝ) ^ 2)⁻¹)
        ≤ (1 : ℝ) / 2 - (((K - 1 : ℕ) : ℝ))⁻¹ := by
      have hb := sum_Ioc_inv_sq_le_sub (α := ℝ) (k := 2) (n := K - 1) (by norm_num) (by omega)
      norm_num at hb ⊢
      linarith
    have hx : 0 ≤ (((K - 1 : ℕ) : ℝ))⁻¹ := by
      exact inv_nonneg.mpr (by positivity)
    norm_num
    nlinarith
  · have hsum0 : (∑ n ∈ Finset.range K, (if 2 ≤ n then ((n : ℝ) ^ 2)⁻¹ else 0)) = 0 := by
      apply Finset.sum_eq_zero
      intro n hn
      have hnlt : n < K := Finset.mem_range.mp hn
      have : ¬ 2 ≤ n := by omega
      simp [this]
    rw [hsum0]
    norm_num

/-- If the `n ≥ 2` terms of the L-series of `f` are bounded by `1/n²`, then the whole
series stays within distance `3/4` of its constant term `f 1 = 1`. -/
private lemma norm_LSeries_sub_one_le {f : ℕ → ℂ} {s : ℂ} (hf1 : f 1 = 1)
    (hsum : LSeriesSummable f s)
    (hterm : ∀ n : ℕ, 2 ≤ n → ‖LSeries.term f s n‖ ≤ ((n : ℝ) ^ 2)⁻¹) :
    ‖LSeries f s - 1‖ ≤ 3 / 4 := by
  let a : ℕ → ℂ := LSeries.term f s
  let c : ℕ → ℂ := fun n => if n = 1 then 0 else a n
  let guard : ℕ → ℝ := fun n => if 2 ≤ n then ((n : ℝ) ^ 2)⁻¹ else 0
  have hc_le_guard : ∀ n : ℕ, ‖c n‖ ≤ guard n := by
    intro n
    by_cases hn1 : n = 1
    · subst n
      simp [c, guard]
    · by_cases hn0 : n = 0
      · subst n
        simp [c, guard, a]
      · have h2 : 2 ≤ n := by omega
        have hc : c n = a n := by simp [c, hn1]
        have hg : guard n = ((n : ℝ) ^ 2)⁻¹ := by simp [guard, h2]
        rw [hc, hg]
        exact hterm n h2
  have hnonneg : ∀ n : ℕ, 0 ≤ ‖c n‖ := fun n => norm_nonneg _
  have hps : ∀ K : ℕ, (∑ i ∈ Finset.range K, ‖c i‖) ≤ 3 / 4 := by
    intro K
    calc
      (∑ i ∈ Finset.range K, ‖c i‖) ≤ ∑ i ∈ Finset.range K, guard i := by
        exact Finset.sum_le_sum (fun i _ => hc_le_guard i)
      _ ≤ 3 / 4 := partial_sum_guard_le K
  have hsumm_c_norm : Summable (fun n => ‖c n‖) := summable_of_sum_range_le hnonneg hps
  have htsum_c_norm : (∑' n, ‖c n‖) ≤ 3 / 4 := Real.tsum_le_of_sum_range_le hnonneg hps
  have htail : (∑' n, c n) = (∑' n, a n) - 1 := by
    have hsum_a : Summable a := hsum
    have hsplit := Summable.tsum_eq_add_tsum_ite (f := a) hsum_a (b := 1)
    have ha1 : a 1 = 1 := by
      simp [a, hf1]
    calc
      (∑' n, c n) = (a 1 + ∑' n, c n) - a 1 := by ring
      _ = (∑' n, a n) - 1 := by
        rw [← hsplit]
        rw [ha1]
  have hL : LSeries f s - 1 = (∑' n, c n) := by
    change (∑' n : ℕ, LSeries.term f s n) - 1 = (∑' n : ℕ, c n)
    rw [← htail]
  have hnorm : ‖(∑' n, c n)‖ ≤ 3 / 4 := (norm_tsum_le_tsum_norm hsumm_c_norm).trans htsum_c_norm
  rw [hL]
  exact hnorm

/-- Coefficient bound `|χ(n)| / n² ≤ 1 / n²` on the line `Re s = 2`. -/
private lemma char_term_sq_bound {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (T : ℝ)
    {n : ℕ} (hn : 2 ≤ n) :
    ‖LSeries.term (fun m : ℕ => (χ (m : ZMod N) : ℂ)) ((2 : ℂ) + Complex.I * (T : ℂ)) n‖
      ≤ ((n : ℝ) ^ 2)⁻¹ := by
  rw [LSeries.norm_term_eq]
  have hn0 : n ≠ 0 := by omega
  rw [if_neg hn0]
  have hs : (((2 : ℂ) + Complex.I * (T : ℂ))).re = 2 := by simp
  rw [hs]
  norm_num
  rw [← one_div]
  exact div_le_div_of_nonneg_right (by simpa using (norm_le_one χ (n : ZMod N))) (sq_nonneg _)

/-- Explicit uniform lower bound at `Re s = 2`: for every non-trivial Dirichlet character `χ`
mod `N` and every real `T`, `|L(χ, 2 + iT)| ≥ 1/4`. -/
theorem L_lower_re_two_explicit {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1)
    (T : ℝ) : (1 : ℝ) / 4 ≤ ‖DirichletCharacter.LFunction χ ((2 : ℂ) + Complex.I * (T : ℂ))‖ := by
  let f : ℕ → ℂ := fun m : ℕ => (χ (m : ZMod N) : ℂ)
  let s : ℂ := (2 : ℂ) + Complex.I * (T : ℂ)
  have hs : 1 < s.re := by simp [s]
  have hsum : LSeriesSummable f s := by
    simpa [f] using DirichletCharacter.LSeriesSummable_of_one_lt_re χ hs
  have hf1 : f 1 = 1 := by
    simp [f]
  have hterm : ∀ n : ℕ, 2 ≤ n → ‖LSeries.term f s n‖ ≤ ((n : ℝ) ^ 2)⁻¹ := by
    intro n hn
    simpa [f, s] using char_term_sq_bound χ T hn
  have hnorm_series : ‖LSeries f s - 1‖ ≤ 3 / 4 :=
    norm_LSeries_sub_one_le (f := f) (s := s) hf1 hsum hterm
  have hLF : LFunction χ s = LSeries f s := by
    simpa [f] using DirichletCharacter.LFunction_eq_LSeries χ hs
  have hnormLF : ‖LFunction χ s - 1‖ ≤ 3 / 4 := by
    rw [hLF]
    exact hnorm_series
  have htri : ‖(1 : ℂ)‖ - ‖LFunction χ s‖ ≤ ‖LFunction χ s - 1‖ := by
    simpa [norm_sub_rev] using norm_sub_norm_le (a := (1 : ℂ)) (b := LFunction χ s)
  have hmain : (1 : ℝ) / 4 ≤ ‖LFunction χ s‖ := by
    have h2 : ‖(1 : ℂ)‖ - ‖LFunction χ s‖ ≤ 3 / 4 := htri.trans hnormLF
    have h3 : (1 : ℝ) - ‖LFunction χ s‖ ≤ 3 / 4 := by simpa using h2
    linarith
  simpa [s] using hmain

end Commons.NumberTheory.DirichletCharacter
