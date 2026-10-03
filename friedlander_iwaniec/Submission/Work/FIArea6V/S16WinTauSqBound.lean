/-
# `Submission.Work.FIArea6V.S16WinTauSqBound` — the norm-window mass bound

`winTauSq Pa = Σ_{⌊N⌋+1 ≤ n ≤ ⌊(1+θ)N⌋} τ(n)²` is bounded by `C·N·(log N)³`, uniformly in
every parameter of `Work.FITop.Params` as soon as `x ≥ e⁸`.

The proof is purely arithmetic:

* `θ = (log x)^{-A'} ≤ 1` (since `log x ≥ 8 ≥ 1` and `A' > 0`), so the window
  `⌊(1+θ)N⌋₊` is contained in `⌊2N⌋₊`;
* the sum is therefore a sub-sum of `Σ_{n ≤ ⌊2N⌋₊} τ(n)²`, estimated by the classical
  `Commons.NumberTheory.DivisorSum.sum_tau_pow_le 2`;
* `⌊2N⌋₊ ≤ 2N` and `log(⌊2N⌋₊ + 1) ≤ 2 log N`, the latter because `N > exp 2 ≥ 3`
  (from `(4.6)`: `N > x^{1/4+η} ≥ (e⁸)^{1/4} = e²`).
-/
import Mathlib
import Submission.Work.FIArea6V.CleanVDefs
import Submission.Commons.NumberTheory.DivisorSum.sum_tau_pow_le

set_option autoImplicit false

namespace Work.FIArea6V

open Finset
open scoped BigOperators

theorem S16WinTauSqBound :
    ∃ C : ℝ, 0 < C ∧ ∀ Pa : Work.FITop.Params, Real.exp 8 ≤ (Pa.x : ℝ) →
      Work.FIArea6V.winTauSq Pa ≤ C * Pa.N * (Real.log Pa.N) ^ (3 : ℕ) := by
  obtain ⟨C0, hC0pos, hC0⟩ :=
    _root_.Commons.NumberTheory.DivisorSum.sum_tau_pow_le 2
  refine ⟨16 * C0, by positivity, ?_⟩
  intro Pa hx
  -- ### Basic facts about the parameters
  have hxpos : (0 : ℝ) < (Pa.x : ℝ) := lt_of_lt_of_le (Real.exp_pos 8) hx
  have hx1 : (1 : ℝ) ≤ (Pa.x : ℝ) :=
    le_trans (Real.one_le_exp (by norm_num)) hx
  have hlog8 : (8 : ℝ) ≤ Real.log (Pa.x : ℝ) := by
    have h := Real.log_le_log (Real.exp_pos 8) hx
    rwa [Real.log_exp] at h
  have hA'pos : 0 < Pa.A' := by
    have h2A : 0 < 2 * Pa.A := by linarith [Pa.hA]
    have h220 : (0 : ℝ) < (2 : ℝ) ^ (20 : ℕ) := by norm_num
    linarith [Pa.hA', h2A, h220]
  have hθle1 : Pa.θ ≤ 1 := by
    rw [Pa.hθ]
    exact Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (by linarith)
  have hN1 : (1 : ℝ) ≤ Pa.N := Pa.hN1
  have hNpos : (0 : ℝ) < Pa.N := by linarith
  -- ### `N > exp 2`
  have hN3 : (3 : ℝ) ≤ Pa.N := by
    have h1 : (Real.exp 8) ^ ((1 : ℝ) / 4) ≤ (Pa.x : ℝ) ^ ((1 : ℝ) / 4) :=
      Real.rpow_le_rpow (Real.exp_pos 8).le hx (by norm_num)
    have h2 : (Real.exp 8) ^ ((1 : ℝ) / 4) = Real.exp 2 := by
      rw [← Real.exp_mul]
      congr 1
      norm_num
    have h3 : (Pa.x : ℝ) ^ ((1 : ℝ) / 4) ≤ (Pa.x : ℝ) ^ ((1 : ℝ) / 4 + Pa.η) :=
      Real.rpow_le_rpow_of_exponent_le hx1 (by linarith [Pa.hη])
    have h4 : Real.exp 2 < Pa.N :=
      lt_of_le_of_lt (le_trans (le_trans (le_of_eq h2.symm) h1) h3) Pa.hNlo
    have h5 : (3 : ℝ) ≤ Real.exp 2 := by have := Real.add_one_le_exp 2; linarith
    linarith
  -- ### The index set of `winTauSq` sits inside `Icc 1 ⌊2N⌋`
  have hfloor : ⌊(1 + Pa.θ) * Pa.N⌋₊ ≤ ⌊2 * Pa.N⌋₊ := by
    refine Nat.floor_mono ?_
    have h : (1 + Pa.θ) ≤ 2 := by linarith
    exact mul_le_mul_of_nonneg_right h hNpos.le
  have hX1 : 1 ≤ ⌊2 * Pa.N⌋₊ := by
    apply Nat.le_floor
    push_cast
    linarith
  have hsub : Finset.Icc (⌊Pa.N⌋₊ + 1) ⌊(1 + Pa.θ) * Pa.N⌋₊ ⊆ Finset.Icc 1 ⌊2 * Pa.N⌋₊ := by
    intro n hn
    simp only [Finset.mem_Icc] at hn ⊢
    exact ⟨by omega, le_trans hn.2 hfloor⟩
  -- ### The divisor-sum bound at `⌊2N⌋`
  have hsum : (∑ n ∈ Finset.Icc 1 ⌊2 * Pa.N⌋₊, ((n.divisors.card : ℝ)) ^ 2)
      ≤ C0 * (⌊2 * Pa.N⌋₊ : ℝ) * (Real.log ((⌊2 * Pa.N⌋₊ : ℝ) + 1)) ^ (3 : ℕ) := by
    have h := hC0 ⌊2 * Pa.N⌋₊ hX1
    rwa [show (2 : ℕ) ^ 2 - 1 = 3 by norm_num] at h
  -- ### `log(⌊2N⌋ + 1) ≤ 2 log N`
  have hXp1_le : (⌊2 * Pa.N⌋₊ : ℝ) + 1 ≤ Pa.N ^ 2 := by
    have h1 : (⌊2 * Pa.N⌋₊ : ℝ) ≤ 2 * Pa.N := Nat.floor_le (by positivity)
    have h2 : 3 * Pa.N ≤ Pa.N ^ 2 := by nlinarith [hN3, hN1]
    have h3 : 2 * Pa.N + 1 ≤ 3 * Pa.N := by linarith
    linarith
  have hlog2 : Real.log ((⌊2 * Pa.N⌋₊ : ℝ) + 1) ≤ 2 * Real.log Pa.N := by
    have hpos : (0 : ℝ) < (⌊2 * Pa.N⌋₊ : ℝ) + 1 := by positivity
    have h := Real.log_le_log hpos hXp1_le
    rw [Real.log_pow] at h
    push_cast at h
    linarith
  have hlognn : (0 : ℝ) ≤ Real.log Pa.N := Real.log_nonneg hN1
  have hlnn : (0 : ℝ) ≤ Real.log ((⌊2 * Pa.N⌋₊ : ℝ) + 1) :=
    Real.log_nonneg (by linarith [Nat.cast_nonneg (α := ℝ) ⌊2 * Pa.N⌋₊])
  have hpow : (Real.log ((⌊2 * Pa.N⌋₊ : ℝ) + 1)) ^ (3 : ℕ)
      ≤ (2 * Real.log Pa.N) ^ (3 : ℕ) := pow_le_pow_left₀ hlnn hlog2 3
  have hXle : (⌊2 * Pa.N⌋₊ : ℝ) ≤ 2 * Pa.N := Nat.floor_le (by positivity)
  -- ### Assembly
  unfold winTauSq
  calc ∑ n ∈ Finset.Icc (⌊Pa.N⌋₊ + 1) ⌊(1 + Pa.θ) * Pa.N⌋₊, ((n.divisors.card : ℝ)) ^ 2
      ≤ ∑ n ∈ Finset.Icc 1 ⌊2 * Pa.N⌋₊, ((n.divisors.card : ℝ)) ^ 2 :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun i _ _ => by positivity)
    _ ≤ C0 * (⌊2 * Pa.N⌋₊ : ℝ) * (Real.log ((⌊2 * Pa.N⌋₊ : ℝ) + 1)) ^ (3 : ℕ) := hsum
    _ ≤ 16 * C0 * Pa.N * (Real.log Pa.N) ^ (3 : ℕ) := by
        calc C0 * (⌊2 * Pa.N⌋₊ : ℝ) * (Real.log ((⌊2 * Pa.N⌋₊ : ℝ) + 1)) ^ (3 : ℕ)
            ≤ C0 * (2 * Pa.N) * ((2 * Real.log Pa.N) ^ (3 : ℕ)) := by
              apply mul_le_mul
              · exact mul_le_mul_of_nonneg_left hXle hC0pos.le
              · exact hpow
              · exact pow_nonneg hlnn 3
              · positivity
          _ = 16 * C0 * Pa.N * (Real.log Pa.N) ^ (3 : ℕ) := by ring

end Work.FIArea6V
