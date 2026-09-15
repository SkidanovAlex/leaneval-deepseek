import Mathlib.NumberTheory.LSeries.DirichletContinuation
import Mathlib.NumberTheory.ZetaValues
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# Lower bound for the real part of a Dirichlet L-function on `Re s ≥ 2`

For a non-principal Dirichlet character `χ` and `s` with `Re s ≥ 2`, the real part of
`L(χ, s)` is bounded below by `1/4`.

The proof is elementary: on `Re s ≥ 2` the Dirichlet series of `L(χ, s)` consists of the
constant term `1` plus a tail which is bounded in modulus by `∑_{n ≥ 2} n^{-2} = π²/6 - 1 < 3/4`.
Hence `L(χ, s) = 1 + (small)`, and taking real parts gives `Re L(χ, s) ≥ 1 - 3/4 = 1/4`.
-/

open Complex DirichletCharacter
open scoped BigOperators

set_option linter.unusedVariables false

namespace Commons.NumberTheory.DirichletCharacter

/-- The "tail" majorant `∑_{n ≥ 2} 1/n²` (as a `tsum`) is at most `3/4`. -/
private lemma tsum_guard_le_three_quarters :
    (∑' n : ℕ, (if 2 ≤ n then ((n : ℝ) ^ 2)⁻¹ else 0)) ≤ 3 / 4 := by
  have hzeta_summ : Summable (fun n : ℕ => ((n : ℝ) ^ 2)⁻¹) := by
    simpa only [one_div] using hasSum_zeta_two.summable
  have hsplit := Summable.tsum_eq_add_tsum_ite hzeta_summ (b := 1)
  have hfun : (fun n : ℕ => (if n = 1 then (0 : ℝ) else ((n : ℝ) ^ 2)⁻¹))
      = fun n : ℕ => if 2 ≤ n then ((n : ℝ) ^ 2)⁻¹ else 0 := by
    funext n
    by_cases h2 : 2 ≤ n
    · have hn1 : n ≠ 1 := by omega
      simp [h2, hn1]
    · have hn : n = 1 ∨ n = 0 := by omega
      rcases hn with rfl | rfl <;> norm_num
  rw [hfun] at hsplit
  simp only [Nat.cast_one, one_pow, inv_one] at hsplit
  have hzeta : (∑' n : ℕ, ((n : ℝ) ^ 2)⁻¹) = Real.pi ^ 2 / 6 := by
    simpa only [one_div] using hasSum_zeta_two.tsum_eq
  have hpi : Real.pi ^ 2 / 6 ≤ 7 / 4 := by nlinarith [Real.pi_pos, Real.pi_lt_d2]
  linarith

/-- If `f 1 = 1` and the terms of the Dirichlet series of `f` at `s` with `n ≥ 2` are bounded
by `n^{-2}`, then `LSeries f s` is within distance `3/4` of `1`. -/
private lemma norm_LSeries_sub_one_le {f : ℕ → ℂ} {s : ℂ} (hf1 : f 1 = 1)
    (hsum : LSeriesSummable f s)
    (hterm : ∀ n : ℕ, 2 ≤ n → ‖LSeries.term f s n‖ ≤ ((n : ℝ) ^ 2)⁻¹) :
    ‖LSeries f s - 1‖ ≤ 3 / 4 := by
  let a : ℕ → ℂ := LSeries.term f s
  let c : ℕ → ℂ := fun n => if n = 1 then 0 else a n
  let g : ℕ → ℝ := fun n => if 2 ≤ n then ((n : ℝ) ^ 2)⁻¹ else 0
  have hsum_a : Summable a := hsum
  have hzeta_summ : Summable (fun n : ℕ => ((n : ℝ) ^ 2)⁻¹) := by
    simpa only [one_div] using hasSum_zeta_two.summable
  have hc_le_g : ∀ n : ℕ, ‖c n‖ ≤ g n := by
    intro n
    by_cases hn1 : n = 1
    · subst n; simp [c, g]
    · by_cases hn0 : n = 0
      · subst n; simp [c, g, a]
      · have h2 : 2 ≤ n := by omega
        have hc : c n = a n := by simp [c, hn1]
        have hgn : g n = ((n : ℝ) ^ 2)⁻¹ := by simp [g, h2]
        rw [hc, hgn]
        exact hterm n h2
  have hg_summ : Summable g := by
    refine Summable.of_nonneg_of_le (fun n => ?_) (fun n => ?_) hzeta_summ
    · by_cases h2 : 2 ≤ n <;> simp [g, h2]
    · by_cases h2 : 2 ≤ n <;> simp [g, h2]
  have hguard : (∑' n : ℕ, g n) ≤ 3 / 4 := tsum_guard_le_three_quarters
  have hc_summ : Summable (fun n : ℕ => ‖c n‖) :=
    Summable.of_nonneg_of_le (fun n => norm_nonneg _) hc_le_g hg_summ
  have htsum_c : (∑' n : ℕ, ‖c n‖) ≤ 3 / 4 :=
    (Summable.tsum_le_tsum hc_le_g hc_summ hg_summ).trans hguard
  have ha1 : a 1 = 1 := by simp [a, hf1]
  have hsplit := Summable.tsum_eq_add_tsum_ite hsum_a (b := 1)
  have hsplit' : (∑' n : ℕ, a n) = a 1 + ∑' n : ℕ, c n := by
    simpa only [c] using hsplit
  have htail : (∑' n : ℕ, c n) = (∑' n : ℕ, a n) - 1 := by
    rw [hsplit', ha1]
    ring
  have hL : LSeries f s - 1 = (∑' n : ℕ, c n) := by
    change (∑' n : ℕ, LSeries.term f s n) - 1 = (∑' n : ℕ, c n)
    rw [← htail]
  rw [hL]
  exact (norm_tsum_le_tsum_norm hc_summ).trans htsum_c

theorem LFunction_re_lower_of_two_le_re {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (hχ : χ ≠ 1) {s : ℂ} (hs : 2 ≤ s.re) : (1 : ℝ) / 4 ≤ (χ.LFunction s).re := by
  have hs1 : 1 < s.re := by linarith
  set f : ℕ → ℂ := fun n => (χ (n : ZMod N) : ℂ) with hf
  have hsum : LSeriesSummable f s := by
    simpa [f] using DirichletCharacter.LSeriesSummable_of_one_lt_re χ hs1
  have hf1 : f 1 = 1 := by simp [f]
  have hterm : ∀ n : ℕ, 2 ≤ n → ‖LSeries.term f s n‖ ≤ ((n : ℝ) ^ 2)⁻¹ := by
    intro n hn
    have hn0 : n ≠ 0 := by omega
    rw [LSeries.norm_term_eq, if_neg hn0]
    have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (by omega : 1 ≤ n)
    have hpow : (n : ℝ) ^ 2 ≤ (n : ℝ) ^ s.re := by
      have := Real.rpow_le_rpow_of_exponent_le hn1 hs
      simpa using this
    have hpos : 0 < (n : ℝ) ^ 2 := by positivity
    calc ‖f n‖ / (n : ℝ) ^ s.re ≤ 1 / (n : ℝ) ^ s.re :=
          div_le_div_of_nonneg_right (by simpa [f] using χ.norm_le_one (n : ZMod N))
            (Real.rpow_nonneg (Nat.cast_nonneg n) _)
      _ ≤ 1 / (n : ℝ) ^ 2 := div_le_div_of_nonneg_left (by norm_num) hpos hpow
      _ = ((n : ℝ) ^ 2)⁻¹ := by rw [one_div]
  have hmain : ‖LSeries f s - 1‖ ≤ 3 / 4 := norm_LSeries_sub_one_le hf1 hsum hterm
  have hLF : χ.LFunction s = LSeries f s := by
    simpa [f] using DirichletCharacter.LFunction_eq_LSeries χ hs1
  have hnormLF : ‖χ.LFunction s - 1‖ ≤ 3 / 4 := by
    rw [hLF]; exact hmain
  have hre : (χ.LFunction s).re = 1 + (χ.LFunction s - 1).re := by
    simp [Complex.sub_re]
  rw [hre]
  have h1 : -|(χ.LFunction s - 1).re| ≤ (χ.LFunction s - 1).re := neg_abs_le _
  have h2 : |(χ.LFunction s - 1).re| ≤ 3 / 4 :=
    (Complex.abs_re_le_norm _).trans hnormLF
  linarith

end Commons.NumberTheory.DirichletCharacter
