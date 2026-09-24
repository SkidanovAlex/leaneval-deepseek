import Mathlib
import Submission.Commons.NumberTheory.BombieriVinogradov.charsum_log_weighted_polyaVinogradov_nontrivial

namespace Commons.NumberTheory.DirichletCharacter

open Finset
open scoped BigOperators

set_option autoImplicit false
set_option linter.style.haveILetI false

/-- For `f` with `f 0 = 0`, the `range N` sum equals the `Icc 1 (N-1)` sum. -/
private lemma sum_range_eq_sum_Icc_pred {f : ℕ → ℂ} (h0 : f 0 = 0) (N : ℕ) :
    ∑ n ∈ Finset.range N, f n = ∑ n ∈ Finset.Icc 1 (N - 1), f n := by
  rcases Nat.eq_zero_or_pos N with hN | hN
  · subst hN; simp
  · have hset : Finset.range N = insert 0 (Finset.Icc 1 (N - 1)) := by
      ext k
      simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]
      omega
    have hmem : (0 : ℕ) ∉ Finset.Icc 1 (N - 1) := by
      simp only [Finset.mem_Icc]; omega
    rw [hset, Finset.sum_insert hmem]
    simp [h0]

/-- Decompose an interval sum in terms of prefix sums starting at `1`. -/
private lemma sum_Icc_eq_sum_Icc_one_sub {f : ℕ → ℂ} (h0 : f 0 = 0) {a b : ℕ} (hab : a ≤ b) :
    ∑ n ∈ Finset.Icc a b, f n
      = (∑ n ∈ Finset.Icc 1 b, f n) - (∑ n ∈ Finset.Icc 1 (a - 1), f n) := by
  have h1 : ∑ n ∈ Finset.Icc a b, f n
      = ∑ n ∈ Finset.range (b + 1), f n - ∑ n ∈ Finset.range a, f n := by
    rw [← Finset.Ico_add_one_right_eq_Icc a b,
      Finset.sum_Ico_eq_sub (f := f) (by omega)]
  rw [h1, sum_range_eq_sum_Icc_pred h0 (b + 1), sum_range_eq_sum_Icc_pred h0 a]
  simp

theorem charSum_logWeighted_range_le_polyaVinogradov :
    ∃ C : ℝ, 0 < C ∧ ∀ (q : ℕ) [_hq : NeZero q] (χ : DirichletCharacter ℂ q) (_hχ : χ ≠ 1)
      (a b : ℕ), a ≤ b →
      ‖∑ n ∈ Finset.Icc a b, ((Real.log (n : ℝ) : ℂ)) * χ (n : ZMod q)‖
        ≤ C * Real.sqrt q * Real.log (2 * (q : ℝ) + 2) * (Real.log (2 * (b : ℝ) + 2)) := by
  obtain ⟨C0, hC0pos, hC0⟩ :=
    Commons.NumberTheory.BombieriVinogradov.charsum_log_weighted_polyaVinogradov_nontrivial
  refine ⟨2 * C0 + 1, by positivity, ?_⟩
  intro q hq χ hχ a b hab
  -- non-negativity facts
  have hsq : (0 : ℝ) ≤ Real.sqrt (q : ℝ) := Real.sqrt_nonneg _
  have hlogq : (0 : ℝ) ≤ Real.log (2 * (q : ℝ) + 2) := by
    apply Real.log_nonneg
    have : (0 : ℝ) ≤ (q : ℝ) := Nat.cast_nonneg q
    linarith
  have hlogb : (0 : ℝ) ≤ Real.log (2 * (b : ℝ) + 2) := by
    apply Real.log_nonneg
    have : (0 : ℝ) ≤ (b : ℝ) := Nat.cast_nonneg b
    linarith
  have hcoef : (0 : ℝ) ≤ C0 * Real.sqrt (q : ℝ) * Real.log (2 * (q : ℝ) + 2) :=
    mul_nonneg (mul_nonneg hC0pos.le hsq) hlogq
  -- bound for the full prefix `Icc 1 b`
  have hgb : ‖∑ n ∈ Finset.Icc 1 b, ((Real.log (n : ℝ) : ℂ)) * χ (n : ZMod q)‖
      ≤ C0 * Real.sqrt (q : ℝ) * Real.log (2 * (q : ℝ) + 2)
          * Real.log (2 * (b : ℝ) + 2) :=
    hC0 q χ hχ b
  -- bound for the truncated prefix `Icc 1 (a-1)`, relaxed to `log (2b+2)`
  have hga : ‖∑ n ∈ Finset.Icc 1 (a - 1), ((Real.log (n : ℝ) : ℂ)) * χ (n : ZMod q)‖
      ≤ C0 * Real.sqrt (q : ℝ) * Real.log (2 * (q : ℝ) + 2)
          * Real.log (2 * (b : ℝ) + 2) := by
    refine (hC0 q χ hχ (a - 1)).trans ?_
    have hle_arg : 2 * (((a - 1 : ℕ) : ℝ)) + 2 ≤ 2 * (b : ℝ) + 2 := by
      have h : ((a - 1 : ℕ) : ℝ) ≤ (b : ℝ) := by
        exact_mod_cast (show a - 1 ≤ b by omega)
      linarith
    have hpos_arg : (0 : ℝ) < 2 * (((a - 1 : ℕ) : ℝ)) + 2 := by
      have : (0 : ℝ) ≤ ((a - 1 : ℕ) : ℝ) := Nat.cast_nonneg _
      linarith
    have hlog_le : Real.log (2 * (((a - 1 : ℕ) : ℝ)) + 2) ≤ Real.log (2 * (b : ℝ) + 2) :=
      Real.log_le_log hpos_arg hle_arg
    exact mul_le_mul_of_nonneg_left hlog_le hcoef
  -- decompose the interval into two prefixes
  have hkey := sum_Icc_eq_sum_Icc_one_sub
    (f := fun n => ((Real.log (n : ℝ) : ℂ)) * χ (n : ZMod q)) (by simp) hab
  calc ‖∑ n ∈ Finset.Icc a b, ((Real.log (n : ℝ) : ℂ)) * χ (n : ZMod q)‖
      = ‖(∑ n ∈ Finset.Icc 1 b, ((Real.log (n : ℝ) : ℂ)) * χ (n : ZMod q))
          - (∑ n ∈ Finset.Icc 1 (a - 1), ((Real.log (n : ℝ) : ℂ)) * χ (n : ZMod q))‖ := by
          rw [hkey]
    _ ≤ ‖∑ n ∈ Finset.Icc 1 b, ((Real.log (n : ℝ) : ℂ)) * χ (n : ZMod q)‖
          + ‖∑ n ∈ Finset.Icc 1 (a - 1), ((Real.log (n : ℝ) : ℂ)) * χ (n : ZMod q)‖ :=
          norm_sub_le _ _
    _ ≤ C0 * Real.sqrt (q : ℝ) * Real.log (2 * (q : ℝ) + 2) * Real.log (2 * (b : ℝ) + 2)
          + C0 * Real.sqrt (q : ℝ) * Real.log (2 * (q : ℝ) + 2) * Real.log (2 * (b : ℝ) + 2) :=
          add_le_add hgb hga
    _ = 2 * C0 * Real.sqrt (q : ℝ) * Real.log (2 * (q : ℝ) + 2) * Real.log (2 * (b : ℝ) + 2) := by
          ring
    _ ≤ (2 * C0 + 1) * Real.sqrt (q : ℝ) * Real.log (2 * (q : ℝ) + 2)
          * Real.log (2 * (b : ℝ) + 2) := by
          have hcoef2 : (0 : ℝ)
              ≤ Real.sqrt (q : ℝ) * Real.log (2 * (q : ℝ) + 2) * Real.log (2 * (b : ℝ) + 2) :=
            mul_nonneg (mul_nonneg hsq hlogq) hlogb
          have hle : 2 * C0 ≤ 2 * C0 + 1 := by linarith
          have := mul_le_mul_of_nonneg_right hle hcoef2
          nlinarith [this]

end Commons.NumberTheory.DirichletCharacter
