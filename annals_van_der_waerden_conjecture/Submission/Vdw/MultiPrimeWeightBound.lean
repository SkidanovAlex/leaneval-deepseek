import Mathlib
import Submission.Vdw.MultiPrimeWeightSumAux
import Submission.Commons.Analysis.Real.pow_sub_pow_le_nsmul
import Submission.Commons.NumberTheory.Nat.card_divisors_le_two_pow_card_primeFactors
import Submission.Commons.NumberTheory.Nat.card_divisors_le_two_pow_card_primeFactors

open Finset
open scoped BigOperators

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option linter.unusedVariables false

/-!
# The reduced frequency sums over the divisors of `C`

This module bounds the divisor sum `Σ_{M | C} M^{-1/2} Wsum M` that arises from
the pattern decomposition of the multi-prime frequency sum
(`MultiPrimeSigma.pattern_sum_le`).

Writing `σ(M) = Σ_{b : ZMod M} freqWeightZ M H b`, we have
`Wsum n H M = σ(M)^n - (2H+1)^n` (`Wsum_eq_sig`), and the two elementary
estimates `σ(M) ≤ (2H+1) + M(1+log M)` (`sig_le`) and
`σ(M) ≤ 5(M+2H+1)(1+log M)` (`sig_le_two`) give, in the two regimes

* `M ≤ 2H+1`: `M^{-1/2}Wsum ≤ n·10^{n-1}(2H+1)^{n-1/2}(1+log C)^n`,
* `2H+1 < M`: `M^{-1/2}Wsum ≤ 10^n·C^{n-1/2}(1+log C)^n`,

using the convexity inequality `a^n - b^n ≤ n(a-b)a^{n-1}`
(`Commons.Analysis.Real.pow_sub_pow_le_nsmul`).

Axioms: propext / Classical.choice / Quot.sound only.
-/

namespace Submission.Vdw
noncomputable section

lemma NeZero_one_le {M : ℕ} [NeZero M] : 1 ≤ M := Nat.one_le_iff_ne_zero.mpr (NeZero.ne M)

/-- The `Wsum` bound in the regime `M ≤ 2H+1`. -/
lemma Wsum_mul_rpow_le_small (n H M C : ℕ) [NeZero M] (hn : 1 ≤ n) (hM2 : M ≤ 2 * H + 1)
    (hMC : M ≤ C) (hC1 : 1 ≤ C) :
    ((M : ℝ) ^ (-(1/2) : ℝ)) * Wsum n H M
      ≤ (n : ℝ) * 10 ^ (n - 1) * (((2 * H + 1 : ℕ)) : ℝ) ^ ((n : ℝ) - 1/2)
          * (1 + Real.log C) ^ n := by
  have hMne : M ≠ 0 := NeZero.ne M
  have hM1 : (1 : ℕ) ≤ M := NeZero_one_le
  have hMR1 : (1 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM1
  have hCR1 : (1 : ℝ) ≤ (C : ℝ) := by exact_mod_cast hC1
  set R : ℝ := (((2 * H + 1 : ℕ)) : ℝ) with hR
  have hR0 : 0 ≤ R := by rw [hR]; positivity
  have hR1 : 1 ≤ R := by rw [hR]; exact_mod_cast (by omega : 1 ≤ 2 * H + 1)
  -- σ ≥ R and σ - R ≤ M(1+log M), σ ≤ 10 R (1+log M)
  have hσR : R ≤ sig H M := sig_le_self H M
  have hσsub : sig H M - R ≤ (M : ℝ) * (1 + Real.log M) := by
    have := sig_le H M
    linarith
  have hσbig : sig H M ≤ 10 * R * (1 + Real.log M) := by
    have h1 := sig_le_two H M
    have h2 : (M : ℝ) + R ≤ 2 * R := by
      have : (M : ℝ) ≤ R := by
        rw [hR]; exact_mod_cast hM2
      linarith
    nlinarith [h1, h2, Real.log_nonneg hMR1]
  -- the convexity step
  have hconv := Commons.Analysis.Real.pow_sub_pow_le_nsmul (sig H M) R n (by rw [hR]; positivity) hσR hn
  have hWle : Wsum n H M ≤ (n : ℝ) * ((M : ℝ) * (1 + Real.log M))
      * (10 * R * (1 + Real.log M)) ^ (n - 1) := by
    have h1 : Wsum n H M = (sig H M) ^ n - R ^ n := by
      rw [Wsum_eq_sig n H M hMne, hR]
    rw [h1]
    refine le_trans hconv ?_
    have hA0 : 0 ≤ (n : ℝ) * (sig H M - R) := by
      have : 0 ≤ sig H M - R := by linarith
      positivity
    have hB : 0 ≤ sig H M := le_trans hR0 hσR
    have hpow : (sig H M) ^ (n - 1) ≤ (10 * R * (1 + Real.log M)) ^ (n - 1) :=
      pow_le_pow_left₀ hB hσbig _
    calc (n : ℝ) * (sig H M - R) * (sig H M) ^ (n - 1)
        ≤ (n : ℝ) * ((M : ℝ) * (1 + Real.log M)) * (sig H M) ^ (n - 1) := by
          refine mul_le_mul_of_nonneg_right ?_ (by positivity)
          exact mul_le_mul_of_nonneg_left hσsub (by positivity)
      _ ≤ (n : ℝ) * ((M : ℝ) * (1 + Real.log M)) * (10 * R * (1 + Real.log M)) ^ (n - 1) :=
          mul_le_mul_of_nonneg_left hpow (by positivity)
  -- multiply by M^{-1/2}
  have hlogM : 1 + Real.log M ≤ 1 + Real.log C := by
    have hMC' : (M : ℝ) ≤ (C : ℝ) := by exact_mod_cast hMC
    have := Real.log_le_log (show (0 : ℝ) < M by positivity) hMC'
    linarith
  have hlog0 : 0 ≤ 1 + Real.log M := by
    have := Real.log_nonneg hMR1; linarith
  have hlogC0 : 0 ≤ 1 + Real.log C := by
    have := Real.log_nonneg hCR1; linarith
  have h1 : Wsum n H M ≤ (n : ℝ) * 10 ^ (n - 1) * ((M : ℝ) * R ^ (n - 1)) * (1 + Real.log C) ^ n := by
    refine le_trans hWle ?_
    have h10 : (10 * R * (1 + Real.log M)) ^ (n - 1)
        = 10 ^ (n - 1) * R ^ (n - 1) * (1 + Real.log M) ^ (n - 1) := by
      rw [mul_pow, mul_pow]
    rw [h10]
    have hlogp : (1 + Real.log M) * (1 + Real.log M) ^ (n - 1)
        ≤ (1 + Real.log C) ^ n := by
      have h2 : (1 + Real.log M) * (1 + Real.log M) ^ (n - 1) = (1 + Real.log M) ^ n := by
        rw [mul_comm, ← pow_succ, Nat.sub_add_cancel hn]
      rw [h2]
      exact pow_le_pow_left₀ hlog0 hlogM n
    have hA : 0 ≤ (n : ℝ) * 10 ^ (n - 1) * ((M : ℝ) * R ^ (n - 1)) := by positivity
    calc (n : ℝ) * ((M : ℝ) * (1 + Real.log M)) * (10 ^ (n - 1) * R ^ (n - 1)
          * (1 + Real.log M) ^ (n - 1))
        = ((n : ℝ) * 10 ^ (n - 1) * ((M : ℝ) * R ^ (n - 1)))
          * ((1 + Real.log M) * (1 + Real.log M) ^ (n - 1)) := by ring
      _ ≤ ((n : ℝ) * 10 ^ (n - 1) * ((M : ℝ) * R ^ (n - 1))) * (1 + Real.log C) ^ n :=
          mul_le_mul_of_nonneg_left hlogp hA
  -- now multiply by M^{-1/2} and use the power arithmetic
  have hM12 : (M : ℝ) ^ (-(1/2) : ℝ) * (M : ℝ) = (M : ℝ) ^ (1/2 : ℝ) := by
    nth_rewrite 2 [← Real.rpow_one (M : ℝ)]
    rw [← Real.rpow_add (by positivity)]
    norm_num
  have hRH : R ^ (n - 1) * R ^ (1/2 : ℝ) = R ^ ((n : ℝ) - 1/2) := by
    rw [← Real.rpow_natCast R (n - 1), ← Real.rpow_add (by linarith)]
    congr 1
    have hn1 : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
      rw [Nat.cast_sub hn]; norm_num
    rw [hn1]; ring
  have hMR12 : (M : ℝ) ^ (1/2 : ℝ) ≤ R ^ (1/2 : ℝ) := by
    have hMR : (M : ℝ) ≤ R := by rw [hR]; exact_mod_cast hM2
    exact Real.rpow_le_rpow (by positivity) hMR (by norm_num)
  calc (M : ℝ) ^ (-(1/2) : ℝ) * Wsum n H M
      ≤ (M : ℝ) ^ (-(1/2) : ℝ)
          * ((n : ℝ) * 10 ^ (n - 1) * ((M : ℝ) * R ^ (n - 1)) * (1 + Real.log C) ^ n) :=
        mul_le_mul_of_nonneg_left h1 (Real.rpow_nonneg (by positivity) _)
    _ = ((n : ℝ) * 10 ^ (n - 1)) * ((M : ℝ) ^ (-(1/2) : ℝ) * (M : ℝ))
          * R ^ (n - 1) * (1 + Real.log C) ^ n := by ring_nf
    _ = ((n : ℝ) * 10 ^ (n - 1)) * (M : ℝ) ^ (1/2 : ℝ) * R ^ (n - 1)
          * (1 + Real.log C) ^ n := by rw [hM12]
    _ ≤ ((n : ℝ) * 10 ^ (n - 1)) * R ^ (1/2 : ℝ) * R ^ (n - 1)
          * (1 + Real.log C) ^ n := by
        have h2 := mul_le_mul_of_nonneg_left hMR12
          (show (0 : ℝ) ≤ (n : ℝ) * 10 ^ (n - 1) by positivity)
        have h3 := mul_le_mul_of_nonneg_right h2 (show (0 : ℝ) ≤ R ^ (n - 1) by positivity)
        have h4 := mul_le_mul_of_nonneg_right h3
          (show (0 : ℝ) ≤ (1 + Real.log C) ^ n by positivity)
        exact h4
    _ = ((n : ℝ) * 10 ^ (n - 1)) * R ^ ((n : ℝ) - 1/2) * (1 + Real.log C) ^ n := by
        rw [mul_assoc ((n : ℝ) * 10 ^ (n - 1)), mul_assoc ((n : ℝ) * 10 ^ (n - 1)),
          mul_comm (R ^ (1/2 : ℝ)) (R ^ (n - 1)), ← mul_assoc, hRH]

/-- The `Wsum` bound in the regime `2H+1 < M`. -/
lemma Wsum_mul_rpow_le_big (n H M C : ℕ) [NeZero M] (hn : 1 ≤ n) (hM2 : 2 * H + 1 < M)
    (hMC : M ≤ C) (hC1 : 1 ≤ C) :
    ((M : ℝ) ^ (-(1/2) : ℝ)) * Wsum n H M
      ≤ 10 ^ n * (C : ℝ) ^ ((n : ℝ) - 1/2) * (1 + Real.log C) ^ n := by
  have hMne : M ≠ 0 := NeZero.ne M
  have hM1 : (1 : ℕ) ≤ M := NeZero_one_le
  have hMR1 : (1 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM1
  have hCR1 : (1 : ℝ) ≤ (C : ℝ) := by exact_mod_cast hC1
  have hMC' : (M : ℝ) ≤ (C : ℝ) := by exact_mod_cast hMC
  have hM2' : (2 : ℝ) * H + 1 < (M : ℝ) := by exact_mod_cast hM2
  have hlog0 : 0 ≤ 1 + Real.log M := by
    have := Real.log_nonneg hMR1; linarith
  have hlogM : 1 + Real.log M ≤ 1 + Real.log C := by
    have := Real.log_le_log (show (0 : ℝ) < M by positivity) hMC'
    linarith
  have hσ : sig H M ≤ 10 * (M : ℝ) * (1 + Real.log M) := by
    have h1 := sig_le_two H M
    have h2 : (M : ℝ) + (((2 * H + 1 : ℕ)) : ℝ) ≤ 2 * (M : ℝ) := by
      push_cast
      linarith
    nlinarith [h1, h2, hlog0, hMR1]
  have hW : Wsum n H M ≤ 10 ^ n * (M : ℝ) ^ n * (1 + Real.log M) ^ n := by
    refine le_trans (Wsum_le_sig_pow n H M hMne) ?_
    have h0 : 0 ≤ sig H M := sig_nonneg H M
    have hpow : (sig H M) ^ n ≤ (10 * (M : ℝ) * (1 + Real.log M)) ^ n :=
      pow_le_pow_left₀ h0 hσ n
    refine le_trans hpow (le_of_eq ?_)
    rw [mul_pow, mul_pow]
  have hM12 : (M : ℝ) ^ (-(1/2) : ℝ) * (M : ℝ) ^ n = (M : ℝ) ^ ((n : ℝ) - 1/2) := by
    rw [← Real.rpow_natCast (M : ℝ) n, ← Real.rpow_add (by positivity)]
    congr 1
    ring
  have hn12 : (0 : ℝ) ≤ (n : ℝ) - 1/2 := by
    have : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    linarith
  have hCr : (M : ℝ) ^ ((n : ℝ) - 1/2) ≤ (C : ℝ) ^ ((n : ℝ) - 1/2) :=
    Real.rpow_le_rpow (by positivity) hMC' hn12
  calc (M : ℝ) ^ (-(1/2) : ℝ) * Wsum n H M
      ≤ (M : ℝ) ^ (-(1/2) : ℝ) * (10 ^ n * (M : ℝ) ^ n * (1 + Real.log M) ^ n) :=
        mul_le_mul_of_nonneg_left hW (Real.rpow_nonneg (by positivity) _)
    _ = 10 ^ n * ((M : ℝ) ^ (-(1/2) : ℝ) * (M : ℝ) ^ n) * (1 + Real.log M) ^ n := by ring
    _ = 10 ^ n * (M : ℝ) ^ ((n : ℝ) - 1/2) * (1 + Real.log M) ^ n := by rw [hM12]
    _ ≤ 10 ^ n * (C : ℝ) ^ ((n : ℝ) - 1/2) * (1 + Real.log C) ^ n := by
        have h2 := mul_le_mul_of_nonneg_left hCr (show (0 : ℝ) ≤ 10 ^ n by positivity)
        have h3 := mul_le_mul_of_nonneg_right h2 (show (0 : ℝ) ≤ (1 + Real.log M) ^ n by positivity)
        have h4 := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hlog0 hlogM n)
          (show (0 : ℝ) ≤ 10 ^ n * (C : ℝ) ^ ((n : ℝ) - 1/2) by positivity)
        exact le_trans h3 (by
          rw [mul_assoc] at h4 ⊢
          exact h4)

/-- **The small-`M` core estimate**: `(2H+1)^{n-1/2}(1+log C)^n ≤ 3^n H^n` in the
regime `(1+log C)^n ≤ √H`. -/
lemma small_core (n H C : ℕ) (hn : 1 ≤ n) (hH1 : 1 ≤ H)
    (hlog2 : (1 + Real.log C) ^ n ≤ (H : ℝ) ^ (1 / 2 : ℝ)) :
    (((2 * H + 1 : ℕ)) : ℝ) ^ ((n : ℝ) - 1/2) * (1 + Real.log C) ^ n
      ≤ (3 : ℝ) ^ n * (H : ℝ) ^ n := by
  have hH1' : (1 : ℝ) ≤ (H : ℝ) := by exact_mod_cast hH1
  have hexp0 : (0 : ℝ) ≤ (n : ℝ) - 1 / 2 := by
    have : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    linarith
  have h3H : (((2 * H + 1 : ℕ)) : ℝ) ≤ 3 * (H : ℝ) := by
    have h2 : (((2 * H + 1 : ℕ)) : ℝ) = 2 * (H : ℝ) + 1 := by push_cast; ring
    rw [h2]; linarith
  have hp1 : (((2 * H + 1 : ℕ)) : ℝ) ^ ((n : ℝ) - 1/2) ≤ (3 * (H : ℝ)) ^ ((n : ℝ) - 1/2) :=
    Real.rpow_le_rpow (by positivity) h3H hexp0
  have hp2 : (3 * (H : ℝ)) ^ ((n : ℝ) - 1/2)
      = (3 : ℝ) ^ ((n : ℝ) - 1/2) * (H : ℝ) ^ ((n : ℝ) - 1/2) :=
    Real.mul_rpow (by norm_num) (by positivity)
  have hp3 : (3 : ℝ) ^ ((n : ℝ) - 1/2) ≤ (3 : ℝ) ^ (n : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) (by push_cast; linarith)
  have hp4 : (H : ℝ) ^ ((n : ℝ) - 1/2) * (H : ℝ) ^ (1/2 : ℝ) = (H : ℝ) ^ n := by
    rw [← Real.rpow_natCast (H : ℝ) n, ← Real.rpow_add (by positivity)]
    congr 1
    ring
  have h1 : (((2 * H + 1 : ℕ)) : ℝ) ^ ((n : ℝ) - 1/2)
      ≤ (3 : ℝ) ^ n * (H : ℝ) ^ ((n : ℝ) - 1/2) := by
    calc (((2 * H + 1 : ℕ)) : ℝ) ^ ((n : ℝ) - 1/2)
        ≤ (3 * (H : ℝ)) ^ ((n : ℝ) - 1/2) := hp1
      _ = (3 : ℝ) ^ ((n : ℝ) - 1/2) * (H : ℝ) ^ ((n : ℝ) - 1/2) := hp2
      _ ≤ (3 : ℝ) ^ n * (H : ℝ) ^ ((n : ℝ) - 1/2) := by
          rw [← Real.rpow_natCast (3 : ℝ) n]
          exact mul_le_mul_of_nonneg_right hp3 (by positivity)
  have hmain : (((2 * H + 1 : ℕ)) : ℝ) ^ ((n : ℝ) - 1/2) * (1 + Real.log C) ^ n
      ≤ ((3 : ℝ) ^ n * (H : ℝ) ^ ((n : ℝ) - 1/2)) * (H : ℝ) ^ (1/2 : ℝ) :=
    mul_le_mul h1 hlog2 (by positivity) (by positivity)
  refine le_trans hmain ?_
  rw [show ((3 : ℝ) ^ n * (H : ℝ) ^ ((n : ℝ) - 1/2)) * (H : ℝ) ^ (1/2 : ℝ)
      = (3 : ℝ) ^ n * (H : ℝ) ^ n by rw [mul_assoc, hp4]]

/-- **The large-`M` core estimate**: `C^{n-1/2}(1+log C)^n ≤ H^n` in the regime
`C ≤ H^{1+1/(2n)}` and `(1+log C)^n ≤ H^{1/(4n)}`. -/
lemma big_core (n H C : ℕ) [NeZero C] (hn : 1 ≤ n) (hH1 : 1 ≤ H)
    (hCrad : (C : ℝ) ≤ (H : ℝ) ^ (1 + 1 / (2 * (n : ℝ))))
    (hlog : (1 + Real.log C) ^ n ≤ (H : ℝ) ^ (1 / (4 * (n : ℝ)))) :
    (C : ℝ) ^ ((n : ℝ) - 1/2) * (1 + Real.log C) ^ n ≤ (H : ℝ) ^ n := by
  have hH1' : (1 : ℝ) ≤ (H : ℝ) := by exact_mod_cast hH1
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hexp0 : (0 : ℝ) ≤ (n : ℝ) - 1 / 2 := by
    have : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    linarith
  have hkey : (1 + 1 / (2 * (n : ℝ))) * ((n : ℝ) - 1/2) = (n : ℝ) - 1 / (4 * (n : ℝ)) := by
    field_simp
    ring
  have hCpow : (C : ℝ) ^ ((n : ℝ) - 1/2) ≤ (H : ℝ) ^ ((n : ℝ) - 1 / (4 * (n : ℝ))) := by
    refine le_trans (Real.rpow_le_rpow (by positivity) hCrad hexp0) (le_of_eq ?_)
    rw [← Real.rpow_mul (by positivity), hkey]
  have hpowH2 : (H : ℝ) ^ ((n : ℝ) - 1 / (4 * (n : ℝ))) * (H : ℝ) ^ (1 / (4 * (n : ℝ)))
      = (H : ℝ) ^ n := by
    rw [← Real.rpow_natCast (H : ℝ) n, ← Real.rpow_add (by positivity)]
    congr 1
    field_simp
    ring
  calc (C : ℝ) ^ ((n : ℝ) - 1/2) * (1 + Real.log C) ^ n
      ≤ (H : ℝ) ^ ((n : ℝ) - 1 / (4 * (n : ℝ))) * (H : ℝ) ^ (1 / (4 * (n : ℝ))) :=
        mul_le_mul hCpow hlog (by positivity) (by positivity)
    _ = (H : ℝ) ^ n := hpowH2

/-- **The pointwise bound for `M ∈ C.divisors`**: the scaled reduced sum at a
divisor is at most `(n·10^{n-1}·3^n + 10^n)·H^n` in the regime. -/
lemma Wsum_mul_rpow_le_pointwise (n H C M : ℕ) [NeZero C] (hn : 1 ≤ n) (hC2 : 2 ≤ C)
    (hH1 : 1 ≤ H) (hMdvd : M ∣ C)
    (hCrad : (C : ℝ) ≤ (H : ℝ) ^ (1 + 1 / (2 * (n : ℝ))))
    (hlog : (1 + Real.log C) ^ n ≤ (H : ℝ) ^ (1 / (4 * (n : ℝ))))
    (hlog2 : (1 + Real.log C) ^ n ≤ (H : ℝ) ^ (1 / 2 : ℝ)) :
    ((M : ℝ) ^ (-(1/2) : ℝ)) * Wsum n H M
      ≤ ((((n * 10 ^ (n - 1) * 3 ^ n + 10 ^ n : ℕ)) : ℝ)) * (H : ℝ) ^ n := by
  have hC1 : 1 ≤ C := by omega
  have hMC : M ≤ C := Nat.le_of_dvd (by omega) hMdvd
  have hMne : M ≠ 0 := fun h0 => (Nat.pos_of_dvd_of_pos hMdvd (by omega)).ne' h0
  haveI : NeZero M := ⟨hMne⟩
  have hB : ((n * 10 ^ (n - 1) * 3 ^ n : ℕ) : ℝ) ≤ (((n * 10 ^ (n - 1) * 3 ^ n + 10 ^ n : ℕ)) : ℝ) := by
    exact_mod_cast Nat.le_add_right _ _
  by_cases hcase : M ≤ 2 * H + 1
  · have hsm := Wsum_mul_rpow_le_small n H M C hn hcase hMC hC1
    have hcore := small_core n H C hn hH1 hlog2
    have hmult : (n : ℝ) * 10 ^ (n - 1)
        * ((((2 * H + 1 : ℕ)) : ℝ) ^ ((n : ℝ) - 1/2) * (1 + Real.log C) ^ n)
        ≤ (n : ℝ) * 10 ^ (n - 1) * ((3 : ℝ) ^ n * (H : ℝ) ^ n) :=
      mul_le_mul_of_nonneg_left hcore (by positivity)
    have hstep : (n : ℝ) * 10 ^ (n - 1) * (((2 * H + 1 : ℕ)) : ℝ) ^ ((n : ℝ) - 1/2)
        * (1 + Real.log C) ^ n
        ≤ ((n * 10 ^ (n - 1) * 3 ^ n : ℕ) : ℝ) * (H : ℝ) ^ n := by
      calc (n : ℝ) * 10 ^ (n - 1) * (((2 * H + 1 : ℕ)) : ℝ) ^ ((n : ℝ) - 1/2)
            * (1 + Real.log C) ^ n
          = (n : ℝ) * 10 ^ (n - 1)
            * ((((2 * H + 1 : ℕ)) : ℝ) ^ ((n : ℝ) - 1/2) * (1 + Real.log C) ^ n) := by ring
        _ ≤ (n : ℝ) * 10 ^ (n - 1) * ((3 : ℝ) ^ n * (H : ℝ) ^ n) := hmult
        _ = ((n * 10 ^ (n - 1) * 3 ^ n : ℕ) : ℝ) * (H : ℝ) ^ n := by
            push_cast
            ring
    exact le_trans (le_trans hsm hstep) (mul_le_mul_of_nonneg_right hB (by positivity))
  · push_neg at hcase
    have hbg := Wsum_mul_rpow_le_big n H M C hn hcase hMC hC1
    have hcore := big_core n H C hn hH1 hCrad hlog
    have hstep : 10 ^ n * (C : ℝ) ^ ((n : ℝ) - 1/2) * (1 + Real.log C) ^ n
        ≤ (10 : ℝ) ^ n * (H : ℝ) ^ n := by
      calc 10 ^ n * (C : ℝ) ^ ((n : ℝ) - 1/2) * (1 + Real.log C) ^ n
          = (10 : ℝ) ^ n * ((C : ℝ) ^ ((n : ℝ) - 1/2) * (1 + Real.log C) ^ n) := by ring
        _ ≤ (10 : ℝ) ^ n * (H : ℝ) ^ n :=
            mul_le_mul_of_nonneg_left hcore (by positivity)
    have h10 : (10 : ℝ) ^ n ≤ (((n * 10 ^ (n - 1) * 3 ^ n + 10 ^ n : ℕ)) : ℝ) := by
      have h2 : (10 : ℕ) ^ n ≤ (n * 10 ^ (n - 1) * 3 ^ n + 10 ^ n : ℕ) := Nat.le_add_left _ _
      calc (10 : ℝ) ^ n = (((10 : ℕ) ^ n : ℕ) : ℝ) := (Nat.cast_pow (α := ℝ) 10 n).symm
        _ ≤ (((n * 10 ^ (n - 1) * 3 ^ n + 10 ^ n : ℕ)) : ℝ) := by exact_mod_cast h2
    exact le_trans (le_trans hbg hstep) (mul_le_mul_of_nonneg_right h10 (by positivity))

/-- **The divisor sum bound**: `Σ_{M | C} M^{-1/2} Wsum M ≤ c^{ω(C)} H^n` under the
regime hypotheses `C ≤ H^{1+1/(2n)}` and `(1+log C)^n ≤ H^{1/(4n)}`. -/
theorem divisor_sum_le (n H C : ℕ) [NeZero C] (hn : 1 ≤ n) (hC2 : 2 ≤ C)
    (hH1 : 1 ≤ H)
    (hCsq : C = ∏ p ∈ C.primeFactors, p)
    (hCrad : (C : ℝ) ≤ (H : ℝ) ^ (1 + 1 / (2 * (n : ℝ))))
    (hlog : (1 + Real.log C) ^ n ≤ (H : ℝ) ^ (1 / (4 * (n : ℝ))))
    (hlog2 : (1 + Real.log C) ^ n ≤ (H : ℝ) ^ (1 / 2 : ℝ)) :
    ∑ M ∈ C.divisors, ((M : ℝ) ^ (-(1/2) : ℝ)) * Wsum n H M
      ≤ (((2 * (n * 10 ^ (n - 1) * 3 ^ n + 10 ^ n) : ℕ)) : ℝ) ^ C.primeFactors.card
          * (H : ℝ) ^ n := by
  classical
  have hsum : ∑ M ∈ C.divisors, ((M : ℝ) ^ (-(1/2) : ℝ)) * Wsum n H M
      ≤ (C.divisors.card : ℝ) * (((((n * 10 ^ (n - 1) * 3 ^ n + 10 ^ n : ℕ)) : ℝ)) * (H : ℝ) ^ n) := by
    calc ∑ M ∈ C.divisors, ((M : ℝ) ^ (-(1/2) : ℝ)) * Wsum n H M
        ≤ ∑ _M ∈ C.divisors, (((((n * 10 ^ (n - 1) * 3 ^ n + 10 ^ n : ℕ)) : ℝ)) * (H : ℝ) ^ n) :=
          Finset.sum_le_sum (fun M hM =>
            Wsum_mul_rpow_le_pointwise n H C M hn hC2 hH1 (Nat.mem_divisors.mp hM).1 hCrad hlog hlog2)
      _ = (C.divisors.card : ℝ) * (((((n * 10 ^ (n - 1) * 3 ^ n + 10 ^ n : ℕ)) : ℝ)) * (H : ℝ) ^ n) := by
          rw [Finset.sum_const, nsmul_eq_mul]
  refine le_trans hsum ?_
  have hcard := Commons.NumberTheory.Nat.card_divisors_le_two_pow_card_primeFactors C hCsq
  have hcard' : (C.divisors.card : ℝ) ≤ (2 : ℝ) ^ C.primeFactors.card := by
    calc (C.divisors.card : ℝ) ≤ (((2 ^ C.primeFactors.card : ℕ)) : ℝ) := by exact_mod_cast hcard
      _ = (2 : ℝ) ^ C.primeFactors.card := Nat.cast_pow 2 _
  have hB1n : (1 : ℕ) ≤ (n * 10 ^ (n - 1) * 3 ^ n + 10 ^ n : ℕ) := by
    have h : (1 : ℕ) ≤ 10 ^ n := Nat.one_le_pow n 10 (by norm_num)
    omega
  have hB1 : (1 : ℝ) ≤ ((((n * 10 ^ (n - 1) * 3 ^ n + 10 ^ n : ℕ)) : ℝ)) := by
    exact_mod_cast hB1n
  have homega : 1 ≤ C.primeFactors.card := by
    obtain ⟨q, hq⟩ := Nat.exists_prime_and_dvd (by omega : C ≠ 1)
    exact Finset.card_pos.mpr ⟨q, Nat.mem_primeFactors.mpr ⟨hq.1, hq.2, by omega⟩⟩
  calc (C.divisors.card : ℝ) * (((((n * 10 ^ (n - 1) * 3 ^ n + 10 ^ n : ℕ)) : ℝ)) * (H : ℝ) ^ n)
      ≤ (2 : ℝ) ^ C.primeFactors.card
          * (((((n * 10 ^ (n - 1) * 3 ^ n + 10 ^ n : ℕ)) : ℝ)) * (H : ℝ) ^ n) :=
        mul_le_mul_of_nonneg_right hcard' (by positivity)
    _ ≤ (((2 * (n * 10 ^ (n - 1) * 3 ^ n + 10 ^ n) : ℕ)) : ℝ) ^ C.primeFactors.card
          * (H : ℝ) ^ n := by
        have h2b : (2 : ℝ) ≤ (((2 * (n * 10 ^ (n - 1) * 3 ^ n + 10 ^ n) : ℕ)) : ℝ) := by
          have h3 : (2 : ℕ) ≤ (2 * (n * 10 ^ (n - 1) * 3 ^ n + 10 ^ n) : ℕ) := by omega
          exact_mod_cast h3
        have h2 : (2 : ℝ) ^ C.primeFactors.card
            ≤ (((2 * (n * 10 ^ (n - 1) * 3 ^ n + 10 ^ n) : ℕ)) : ℝ) ^ C.primeFactors.card :=
          pow_le_pow_left₀ (by norm_num) h2b _
        have hBp : ((((n * 10 ^ (n - 1) * 3 ^ n + 10 ^ n : ℕ)) : ℝ))
            ≤ ((((n * 10 ^ (n - 1) * 3 ^ n + 10 ^ n : ℕ)) : ℝ)) ^ C.primeFactors.card := by
          calc ((((n * 10 ^ (n - 1) * 3 ^ n + 10 ^ n : ℕ)) : ℝ))
              = ((((n * 10 ^ (n - 1) * 3 ^ n + 10 ^ n : ℕ)) : ℝ)) ^ 1 := (pow_one _).symm
            _ ≤ ((((n * 10 ^ (n - 1) * 3 ^ n + 10 ^ n : ℕ)) : ℝ)) ^ C.primeFactors.card :=
                pow_le_pow_right₀ hB1 homega
        calc (2 : ℝ) ^ C.primeFactors.card
              * (((((n * 10 ^ (n - 1) * 3 ^ n + 10 ^ n : ℕ)) : ℝ)) * (H : ℝ) ^ n)
            = ((2 : ℝ) ^ C.primeFactors.card
                * ((((n * 10 ^ (n - 1) * 3 ^ n + 10 ^ n : ℕ)) : ℝ))) * (H : ℝ) ^ n := by ring
          _ ≤ ((((2 * (n * 10 ^ (n - 1) * 3 ^ n + 10 ^ n) : ℕ)) : ℝ) ^ C.primeFactors.card)
                * (H : ℝ) ^ n := by
              refine mul_le_mul_of_nonneg_right ?_ (by positivity)
              calc (2 : ℝ) ^ C.primeFactors.card
                    * ((((n * 10 ^ (n - 1) * 3 ^ n + 10 ^ n : ℕ)) : ℝ))
                  ≤ (2 : ℝ) ^ C.primeFactors.card
                    * ((((n * 10 ^ (n - 1) * 3 ^ n + 10 ^ n : ℕ)) : ℝ)) ^ C.primeFactors.card :=
                    mul_le_mul_of_nonneg_left hBp (by positivity)
                _ = ((2 : ℝ) * ((((n * 10 ^ (n - 1) * 3 ^ n + 10 ^ n : ℕ)) : ℝ))) ^ C.primeFactors.card :=
                    (mul_pow _ _ _).symm
                _ = (((2 * (n * 10 ^ (n - 1) * 3 ^ n + 10 ^ n) : ℕ)) : ℝ) ^ C.primeFactors.card := by
                    push_cast
                    ring



/-! ## θ-generic form of the small-`M` regime bound -/

/-- The `Wsum` bound in the regime `M ≤ 2H+1`. -/
lemma Wsum_mul_rpow_le_small_theta (n H M C : ℕ) [NeZero M] (θ : ℝ) (hn : 1 ≤ n)
    (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) (hM2 : M ≤ 2 * H + 1)
    (hMC : M ≤ C) (hC1 : 1 ≤ C) :
    ((M : ℝ) ^ (-θ)) * Wsum n H M
      ≤ (n : ℝ) * 10 ^ (n - 1) * (((2 * H + 1 : ℕ)) : ℝ) ^ ((n : ℝ) - θ)
          * (1 + Real.log C) ^ n := by
  have hMne : M ≠ 0 := NeZero.ne M
  have hM1 : (1 : ℕ) ≤ M := NeZero_one_le
  have hMR1 : (1 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM1
  have hCR1 : (1 : ℝ) ≤ (C : ℝ) := by exact_mod_cast hC1
  set R : ℝ := (((2 * H + 1 : ℕ)) : ℝ) with hR
  have hR0 : 0 ≤ R := by rw [hR]; positivity
  have hR1 : 1 ≤ R := by rw [hR]; exact_mod_cast (by omega : 1 ≤ 2 * H + 1)
  -- σ ≥ R and σ - R ≤ M(1+log M), σ ≤ 10 R (1+log M)
  have hσR : R ≤ sig H M := sig_le_self H M
  have hσsub : sig H M - R ≤ (M : ℝ) * (1 + Real.log M) := by
    have := sig_le H M
    linarith
  have hσbig : sig H M ≤ 10 * R * (1 + Real.log M) := by
    have h1 := sig_le_two H M
    have h2 : (M : ℝ) + R ≤ 2 * R := by
      have : (M : ℝ) ≤ R := by
        rw [hR]; exact_mod_cast hM2
      linarith
    nlinarith [h1, h2, Real.log_nonneg hMR1]
  -- the convexity step
  have hconv := Commons.Analysis.Real.pow_sub_pow_le_nsmul (sig H M) R n (by rw [hR]; positivity) hσR hn
  have hWle : Wsum n H M ≤ (n : ℝ) * ((M : ℝ) * (1 + Real.log M))
      * (10 * R * (1 + Real.log M)) ^ (n - 1) := by
    have h1 : Wsum n H M = (sig H M) ^ n - R ^ n := by
      rw [Wsum_eq_sig n H M hMne, hR]
    rw [h1]
    refine le_trans hconv ?_
    have hA0 : 0 ≤ (n : ℝ) * (sig H M - R) := by
      have : 0 ≤ sig H M - R := by linarith
      positivity
    have hB : 0 ≤ sig H M := le_trans hR0 hσR
    have hpow : (sig H M) ^ (n - 1) ≤ (10 * R * (1 + Real.log M)) ^ (n - 1) :=
      pow_le_pow_left₀ hB hσbig _
    calc (n : ℝ) * (sig H M - R) * (sig H M) ^ (n - 1)
        ≤ (n : ℝ) * ((M : ℝ) * (1 + Real.log M)) * (sig H M) ^ (n - 1) := by
          refine mul_le_mul_of_nonneg_right ?_ (by positivity)
          exact mul_le_mul_of_nonneg_left hσsub (by positivity)
      _ ≤ (n : ℝ) * ((M : ℝ) * (1 + Real.log M)) * (10 * R * (1 + Real.log M)) ^ (n - 1) :=
          mul_le_mul_of_nonneg_left hpow (by positivity)
  -- multiply by M^{-1/2}
  have hlogM : 1 + Real.log M ≤ 1 + Real.log C := by
    have hMC' : (M : ℝ) ≤ (C : ℝ) := by exact_mod_cast hMC
    have := Real.log_le_log (show (0 : ℝ) < M by positivity) hMC'
    linarith
  have hlog0 : 0 ≤ 1 + Real.log M := by
    have := Real.log_nonneg hMR1; linarith
  have hlogC0 : 0 ≤ 1 + Real.log C := by
    have := Real.log_nonneg hCR1; linarith
  have h1 : Wsum n H M ≤ (n : ℝ) * 10 ^ (n - 1) * ((M : ℝ) * R ^ (n - 1)) * (1 + Real.log C) ^ n := by
    refine le_trans hWle ?_
    have h10 : (10 * R * (1 + Real.log M)) ^ (n - 1)
        = 10 ^ (n - 1) * R ^ (n - 1) * (1 + Real.log M) ^ (n - 1) := by
      rw [mul_pow, mul_pow]
    rw [h10]
    have hlogp : (1 + Real.log M) * (1 + Real.log M) ^ (n - 1)
        ≤ (1 + Real.log C) ^ n := by
      have h2 : (1 + Real.log M) * (1 + Real.log M) ^ (n - 1) = (1 + Real.log M) ^ n := by
        rw [mul_comm, ← pow_succ, Nat.sub_add_cancel hn]
      rw [h2]
      exact pow_le_pow_left₀ hlog0 hlogM n
    have hA : 0 ≤ (n : ℝ) * 10 ^ (n - 1) * ((M : ℝ) * R ^ (n - 1)) := by positivity
    calc (n : ℝ) * ((M : ℝ) * (1 + Real.log M)) * (10 ^ (n - 1) * R ^ (n - 1)
          * (1 + Real.log M) ^ (n - 1))
        = ((n : ℝ) * 10 ^ (n - 1) * ((M : ℝ) * R ^ (n - 1)))
          * ((1 + Real.log M) * (1 + Real.log M) ^ (n - 1)) := by ring
      _ ≤ ((n : ℝ) * 10 ^ (n - 1) * ((M : ℝ) * R ^ (n - 1))) * (1 + Real.log C) ^ n :=
          mul_le_mul_of_nonneg_left hlogp hA
  -- now multiply by M^{-1/2} and use the power arithmetic
  have hM12 : (M : ℝ) ^ (-θ) * (M : ℝ) = (M : ℝ) ^ ((1:ℝ) - θ) := by
    nth_rewrite 2 [← Real.rpow_one (M : ℝ)]
    rw [← Real.rpow_add (by positivity)]
    ring
  have hRH : R ^ ((1:ℝ) - θ) * R ^ (n - 1) = R ^ ((n : ℝ) - θ) := by
    rw [← Real.rpow_natCast R (n - 1), ← Real.rpow_add (by linarith)]
    congr 1
    have hn1 : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
      rw [Nat.cast_sub hn]; norm_num
    rw [hn1]; ring
  have hMR12 : (M : ℝ) ^ ((1:ℝ) - θ) ≤ R ^ ((1:ℝ) - θ) := by
    have hMR : (M : ℝ) ≤ R := by rw [hR]; exact_mod_cast hM2
    exact Real.rpow_le_rpow (by positivity) hMR (by linarith)
  calc (M : ℝ) ^ (-θ) * Wsum n H M
      ≤ (M : ℝ) ^ (-θ)
          * ((n : ℝ) * 10 ^ (n - 1) * ((M : ℝ) * R ^ (n - 1)) * (1 + Real.log C) ^ n) :=
        mul_le_mul_of_nonneg_left h1 (Real.rpow_nonneg (by positivity) _)
    _ = ((n : ℝ) * 10 ^ (n - 1)) * ((M : ℝ) ^ (-θ) * (M : ℝ))
          * R ^ (n - 1) * (1 + Real.log C) ^ n := by ring_nf
    _ = ((n : ℝ) * 10 ^ (n - 1)) * (M : ℝ) ^ ((1:ℝ) - θ) * R ^ (n - 1)
          * (1 + Real.log C) ^ n := by rw [hM12]
    _ ≤ ((n : ℝ) * 10 ^ (n - 1)) * R ^ ((1:ℝ) - θ) * R ^ (n - 1)
          * (1 + Real.log C) ^ n := by
        have h2 := mul_le_mul_of_nonneg_left hMR12
          (show (0 : ℝ) ≤ (n : ℝ) * 10 ^ (n - 1) by positivity)
        have h3 := mul_le_mul_of_nonneg_right h2 (show (0 : ℝ) ≤ R ^ (n - 1) by positivity)
        have h4 := mul_le_mul_of_nonneg_right h3
          (show (0 : ℝ) ≤ (1 + Real.log C) ^ n by positivity)
        exact h4
    _ = ((n : ℝ) * 10 ^ (n - 1)) * R ^ ((n : ℝ) - θ) * (1 + Real.log C) ^ n := by
        rw [show ((n : ℝ) * 10 ^ (n - 1)) * R ^ ((1:ℝ) - θ) * R ^ (n - 1) * (1 + Real.log C) ^ n
            = (((n : ℝ) * 10 ^ (n - 1)) * (R ^ ((1:ℝ) - θ) * R ^ (n - 1)))
              * (1 + Real.log C) ^ n from by ring, hRH]



/-! ## θ-generic form of the large-`M` regime bound -/

/-- The `Wsum` bound in the regime `2H+1 < M`. -/
lemma Wsum_mul_rpow_le_big_theta (n H M C : ℕ) [NeZero M] (θ : ℝ) (hn : 1 ≤ n)
    (hθn : θ ≤ (n : ℝ)) (hM2 : 2 * H + 1 < M)
    (hMC : M ≤ C) (hC1 : 1 ≤ C) :
    ((M : ℝ) ^ (-θ)) * Wsum n H M
      ≤ 10 ^ n * (C : ℝ) ^ ((n : ℝ) - θ) * (1 + Real.log C) ^ n := by
  have hMne : M ≠ 0 := NeZero.ne M
  have hM1 : (1 : ℕ) ≤ M := NeZero_one_le
  have hMR1 : (1 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM1
  have hCR1 : (1 : ℝ) ≤ (C : ℝ) := by exact_mod_cast hC1
  have hMC' : (M : ℝ) ≤ (C : ℝ) := by exact_mod_cast hMC
  have hM2' : (2 : ℝ) * H + 1 < (M : ℝ) := by exact_mod_cast hM2
  have hlog0 : 0 ≤ 1 + Real.log M := by
    have := Real.log_nonneg hMR1; linarith
  have hlogM : 1 + Real.log M ≤ 1 + Real.log C := by
    have := Real.log_le_log (show (0 : ℝ) < M by positivity) hMC'
    linarith
  have hσ : sig H M ≤ 10 * (M : ℝ) * (1 + Real.log M) := by
    have h1 := sig_le_two H M
    have h2 : (M : ℝ) + (((2 * H + 1 : ℕ)) : ℝ) ≤ 2 * (M : ℝ) := by
      push_cast
      linarith
    nlinarith [h1, h2, hlog0, hMR1]
  have hW : Wsum n H M ≤ 10 ^ n * (M : ℝ) ^ n * (1 + Real.log M) ^ n := by
    refine le_trans (Wsum_le_sig_pow n H M hMne) ?_
    have h0 : 0 ≤ sig H M := sig_nonneg H M
    have hpow : (sig H M) ^ n ≤ (10 * (M : ℝ) * (1 + Real.log M)) ^ n :=
      pow_le_pow_left₀ h0 hσ n
    refine le_trans hpow (le_of_eq ?_)
    rw [mul_pow, mul_pow]
  have hM12 : (M : ℝ) ^ (-θ) * (M : ℝ) ^ n = (M : ℝ) ^ ((n : ℝ) - θ) := by
    rw [← Real.rpow_natCast (M : ℝ) n, ← Real.rpow_add (by positivity)]
    congr 1
    ring
  have hn12 : (0 : ℝ) ≤ (n : ℝ) - θ := by linarith
  have hCr : (M : ℝ) ^ ((n : ℝ) - θ) ≤ (C : ℝ) ^ ((n : ℝ) - θ) :=
    Real.rpow_le_rpow (by positivity) hMC' hn12
  calc (M : ℝ) ^ (-θ) * Wsum n H M
      ≤ (M : ℝ) ^ (-θ) * (10 ^ n * (M : ℝ) ^ n * (1 + Real.log M) ^ n) :=
        mul_le_mul_of_nonneg_left hW (Real.rpow_nonneg (by positivity) _)
    _ = 10 ^ n * ((M : ℝ) ^ (-θ) * (M : ℝ) ^ n) * (1 + Real.log M) ^ n := by ring
    _ = 10 ^ n * (M : ℝ) ^ ((n : ℝ) - θ) * (1 + Real.log M) ^ n := by rw [hM12]
    _ ≤ 10 ^ n * (C : ℝ) ^ ((n : ℝ) - θ) * (1 + Real.log C) ^ n := by
        have h2 := mul_le_mul_of_nonneg_left hCr (show (0 : ℝ) ≤ 10 ^ n by positivity)
        have h3 := mul_le_mul_of_nonneg_right h2 (show (0 : ℝ) ≤ (1 + Real.log M) ^ n by positivity)
        have h4 := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hlog0 hlogM n)
          (show (0 : ℝ) ≤ 10 ^ n * (C : ℝ) ^ ((n : ℝ) - θ) by positivity)
        exact le_trans h3 (by
          rw [mul_assoc] at h4 ⊢
          exact h4)



/-! ## θ,δ-generic core estimates -/

/-- The generic log gap: the exponent of `H` that the logarithmic factor is
allowed to consume, `g := n - (1+δ)(n-θ)`.  The Case-I regime satisfies
`(1+δ)(n-θ) ≤ n`, so `0 ≤ g`; the Fenchel-type parameter identity
`(1+δ)(n-θ) + g = n` is `logGap_eq`. -/
def logGap (n : ℕ) (θ δ : ℝ) : ℝ := (n : ℝ) - (1 + δ) * ((n : ℝ) - θ)

lemma logGap_eq (n : ℕ) (θ δ : ℝ) : (1 + δ) * ((n : ℝ) - θ) + logGap n θ δ = (n : ℝ) := by
  rw [logGap]; ring

/-- **The small-`M` core estimate, generic form**:
`(2H+1)^{n-θ}(1+log C)^n ≤ 3^n H^n` in the regime `(1+log C)^n ≤ H^θ`. -/
lemma small_core_theta (n H C : ℕ) (θ : ℝ) (hn : 1 ≤ n) (hθ0 : 0 ≤ θ)
    (hθn : θ ≤ (n : ℝ)) (hH1 : 1 ≤ H)
    (hlogθ : (1 + Real.log C) ^ n ≤ (H : ℝ) ^ θ) :
    (((2 * H + 1 : ℕ)) : ℝ) ^ ((n : ℝ) - θ) * (1 + Real.log C) ^ n
      ≤ (3 : ℝ) ^ n * (H : ℝ) ^ n := by
  have hH1' : (1 : ℝ) ≤ (H : ℝ) := by exact_mod_cast hH1
  have hexp0 : (0 : ℝ) ≤ (n : ℝ) - θ := by linarith
  have h3H : (((2 * H + 1 : ℕ)) : ℝ) ≤ 3 * (H : ℝ) := by
    have h2 : (((2 * H + 1 : ℕ)) : ℝ) = 2 * (H : ℝ) + 1 := by push_cast; ring
    rw [h2]; linarith
  have hp1 : (((2 * H + 1 : ℕ)) : ℝ) ^ ((n : ℝ) - θ) ≤ (3 * (H : ℝ)) ^ ((n : ℝ) - θ) :=
    Real.rpow_le_rpow (by positivity) h3H hexp0
  have hp2 : (3 * (H : ℝ)) ^ ((n : ℝ) - θ)
      = (3 : ℝ) ^ ((n : ℝ) - θ) * (H : ℝ) ^ ((n : ℝ) - θ) :=
    Real.mul_rpow (by norm_num) (by positivity)
  have hp3 : (3 : ℝ) ^ ((n : ℝ) - θ) ≤ (3 : ℝ) ^ (n : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
  have hp4 : (H : ℝ) ^ ((n : ℝ) - θ) * (H : ℝ) ^ θ = (H : ℝ) ^ n := by
    rw [← Real.rpow_natCast (H : ℝ) n, ← Real.rpow_add (by positivity)]
    congr 1
    ring
  have h1 : (((2 * H + 1 : ℕ)) : ℝ) ^ ((n : ℝ) - θ)
      ≤ (3 : ℝ) ^ n * (H : ℝ) ^ ((n : ℝ) - θ) := by
    calc (((2 * H + 1 : ℕ)) : ℝ) ^ ((n : ℝ) - θ)
        ≤ (3 * (H : ℝ)) ^ ((n : ℝ) - θ) := hp1
      _ = (3 : ℝ) ^ ((n : ℝ) - θ) * (H : ℝ) ^ ((n : ℝ) - θ) := hp2
      _ ≤ (3 : ℝ) ^ n * (H : ℝ) ^ ((n : ℝ) - θ) := by
          rw [← Real.rpow_natCast (3 : ℝ) n]
          exact mul_le_mul_of_nonneg_right hp3 (by positivity)
  have hmain : (((2 * H + 1 : ℕ)) : ℝ) ^ ((n : ℝ) - θ) * (1 + Real.log C) ^ n
      ≤ ((3 : ℝ) ^ n * (H : ℝ) ^ ((n : ℝ) - θ)) * (H : ℝ) ^ θ :=
    mul_le_mul h1 hlogθ (by positivity) (by positivity)
  refine le_trans hmain ?_
  rw [show ((3 : ℝ) ^ n * (H : ℝ) ^ ((n : ℝ) - θ)) * (H : ℝ) ^ θ
      = (3 : ℝ) ^ n * (H : ℝ) ^ n by rw [mul_assoc, hp4]]

/-- **The large-`M` core estimate, generic form**: `C^{n-θ}(1+log C)^n ≤ H^n`
in the regime `C ≤ H^{1+δ}` and `(1+log C)^n ≤ H^{logGap n θ δ}`. -/
lemma big_core_theta (n H C : ℕ) (θ δ : ℝ) [NeZero C] (hn : 1 ≤ n) (hθn : θ ≤ (n : ℝ))
    (hH1 : 1 ≤ H)
    (hCrad : (C : ℝ) ≤ (H : ℝ) ^ (1 + δ))
    (hlog : (1 + Real.log C) ^ n ≤ (H : ℝ) ^ (logGap n θ δ)) :
    (C : ℝ) ^ ((n : ℝ) - θ) * (1 + Real.log C) ^ n ≤ (H : ℝ) ^ n := by
  have hexp0 : (0 : ℝ) ≤ (n : ℝ) - θ := by linarith
  have hkey : (1 + δ) * ((n : ℝ) - θ) = (n : ℝ) - logGap n θ δ := by
    rw [logGap]; ring
  have hCpow : (C : ℝ) ^ ((n : ℝ) - θ) ≤ (H : ℝ) ^ ((n : ℝ) - logGap n θ δ) := by
    refine le_trans (Real.rpow_le_rpow (by positivity) hCrad hexp0) (le_of_eq ?_)
    rw [← Real.rpow_mul (by positivity), hkey]
  have hpowH2 : (H : ℝ) ^ ((n : ℝ) - logGap n θ δ) * (H : ℝ) ^ (logGap n θ δ)
      = (H : ℝ) ^ n := by
    rw [← Real.rpow_natCast (H : ℝ) n, ← Real.rpow_add (by positivity)]
    congr 1
    rw [logGap]; ring
  calc (C : ℝ) ^ ((n : ℝ) - θ) * (1 + Real.log C) ^ n
      ≤ (H : ℝ) ^ ((n : ℝ) - logGap n θ δ) * (H : ℝ) ^ (logGap n θ δ) :=
        mul_le_mul hCpow hlog (by positivity) (by positivity)
    _ = (H : ℝ) ^ n := hpowH2


/-! ## θ,δ-generic pointwise and divisor-sum bounds -/

/-- **The pointwise bound for `M ∈ C.divisors`**: the scaled reduced sum at a
divisor is at most `(n·10^{n-1}·3^n + 10^n)·H^n` in the regime. -/
lemma Wsum_mul_rpow_le_pointwise_theta (n H C M : ℕ) [NeZero C] (θ δ : ℝ) (hn : 1 ≤ n)
    (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) (hθn : θ ≤ (n : ℝ))
    (hC2 : 2 ≤ C)
    (hH1 : 1 ≤ H) (hMdvd : M ∣ C)
    (hCrad : (C : ℝ) ≤ (H : ℝ) ^ (1 + δ))
    (hlog : (1 + Real.log C) ^ n ≤ (H : ℝ) ^ (logGap n θ δ))
    (hlog2 : (1 + Real.log C) ^ n ≤ (H : ℝ) ^ θ) :
    ((M : ℝ) ^ (-θ)) * Wsum n H M
      ≤ ((((n * 10 ^ (n - 1) * 3 ^ n + 10 ^ n : ℕ)) : ℝ)) * (H : ℝ) ^ n := by
  have hC1 : 1 ≤ C := by omega
  have hMC : M ≤ C := Nat.le_of_dvd (by omega) hMdvd
  have hMne : M ≠ 0 := fun h0 => (Nat.pos_of_dvd_of_pos hMdvd (by omega)).ne' h0
  haveI : NeZero M := ⟨hMne⟩
  have hB : ((n * 10 ^ (n - 1) * 3 ^ n : ℕ) : ℝ) ≤ (((n * 10 ^ (n - 1) * 3 ^ n + 10 ^ n : ℕ)) : ℝ) := by
    exact_mod_cast Nat.le_add_right _ _
  by_cases hcase : M ≤ 2 * H + 1
  · have hsm := Wsum_mul_rpow_le_small_theta n H M C θ hn hθ0 hθ1 hcase hMC hC1
    have hcore := small_core_theta n H C θ hn hθ0 hθn hH1 hlog2
    have hmult : (n : ℝ) * 10 ^ (n - 1)
        * ((((2 * H + 1 : ℕ)) : ℝ) ^ ((n : ℝ) - θ) * (1 + Real.log C) ^ n)
        ≤ (n : ℝ) * 10 ^ (n - 1) * ((3 : ℝ) ^ n * (H : ℝ) ^ n) :=
      mul_le_mul_of_nonneg_left hcore (by positivity)
    have hstep : (n : ℝ) * 10 ^ (n - 1) * (((2 * H + 1 : ℕ)) : ℝ) ^ ((n : ℝ) - θ)
        * (1 + Real.log C) ^ n
        ≤ ((n * 10 ^ (n - 1) * 3 ^ n : ℕ) : ℝ) * (H : ℝ) ^ n := by
      calc (n : ℝ) * 10 ^ (n - 1) * (((2 * H + 1 : ℕ)) : ℝ) ^ ((n : ℝ) - θ)
            * (1 + Real.log C) ^ n
          = (n : ℝ) * 10 ^ (n - 1)
            * ((((2 * H + 1 : ℕ)) : ℝ) ^ ((n : ℝ) - θ) * (1 + Real.log C) ^ n) := by ring
        _ ≤ (n : ℝ) * 10 ^ (n - 1) * ((3 : ℝ) ^ n * (H : ℝ) ^ n) := hmult
        _ = ((n * 10 ^ (n - 1) * 3 ^ n : ℕ) : ℝ) * (H : ℝ) ^ n := by
            push_cast
            ring
    exact le_trans (le_trans hsm hstep) (mul_le_mul_of_nonneg_right hB (by positivity))
  · push_neg at hcase
    have hbg := Wsum_mul_rpow_le_big_theta n H M C θ hn hθn hcase hMC hC1
    have hcore := big_core_theta n H C θ δ hn hθn hH1 hCrad hlog
    have hstep : 10 ^ n * (C : ℝ) ^ ((n : ℝ) - θ) * (1 + Real.log C) ^ n
        ≤ (10 : ℝ) ^ n * (H : ℝ) ^ n := by
      calc 10 ^ n * (C : ℝ) ^ ((n : ℝ) - θ) * (1 + Real.log C) ^ n
          = (10 : ℝ) ^ n * ((C : ℝ) ^ ((n : ℝ) - θ) * (1 + Real.log C) ^ n) := by ring
        _ ≤ (10 : ℝ) ^ n * (H : ℝ) ^ n :=
            mul_le_mul_of_nonneg_left hcore (by positivity)
    have h10 : (10 : ℝ) ^ n ≤ (((n * 10 ^ (n - 1) * 3 ^ n + 10 ^ n : ℕ)) : ℝ) := by
      have h2 : (10 : ℕ) ^ n ≤ (n * 10 ^ (n - 1) * 3 ^ n + 10 ^ n : ℕ) := Nat.le_add_left _ _
      calc (10 : ℝ) ^ n = (((10 : ℕ) ^ n : ℕ) : ℝ) := (Nat.cast_pow (α := ℝ) 10 n).symm
        _ ≤ (((n * 10 ^ (n - 1) * 3 ^ n + 10 ^ n : ℕ)) : ℝ) := by exact_mod_cast h2
    exact le_trans (le_trans hbg hstep) (mul_le_mul_of_nonneg_right h10 (by positivity))


/-- **The divisor sum bound**: `Σ_{M | C} M^{-1/2} Wsum M ≤ c^{ω(C)} H^n` under the
regime hypotheses `C ≤ H^{1+1/(2n)}` and `(1+log C)^n ≤ H^{1/(4n)}`. -/
theorem divisor_sum_le_theta (n H C : ℕ) [NeZero C] (θ δ : ℝ) (hn : 1 ≤ n)
    (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) (hθn : θ ≤ (n : ℝ))
    (hC2 : 2 ≤ C)
    (hH1 : 1 ≤ H)
    (hCsq : C = ∏ p ∈ C.primeFactors, p)
    (hCrad : (C : ℝ) ≤ (H : ℝ) ^ (1 + δ))
    (hlog : (1 + Real.log C) ^ n ≤ (H : ℝ) ^ (logGap n θ δ))
    (hlog2 : (1 + Real.log C) ^ n ≤ (H : ℝ) ^ θ) :
    ∑ M ∈ C.divisors, ((M : ℝ) ^ (-θ)) * Wsum n H M
      ≤ (((2 * (n * 10 ^ (n - 1) * 3 ^ n + 10 ^ n) : ℕ)) : ℝ) ^ C.primeFactors.card
          * (H : ℝ) ^ n := by
  classical
  have hsum : ∑ M ∈ C.divisors, ((M : ℝ) ^ (-θ)) * Wsum n H M
      ≤ (C.divisors.card : ℝ) * (((((n * 10 ^ (n - 1) * 3 ^ n + 10 ^ n : ℕ)) : ℝ)) * (H : ℝ) ^ n) := by
    calc ∑ M ∈ C.divisors, ((M : ℝ) ^ (-θ)) * Wsum n H M
        ≤ ∑ _M ∈ C.divisors, (((((n * 10 ^ (n - 1) * 3 ^ n + 10 ^ n : ℕ)) : ℝ)) * (H : ℝ) ^ n) :=
          Finset.sum_le_sum (fun M hM =>
            Wsum_mul_rpow_le_pointwise_theta n H C M θ δ hn hθ0 hθ1 hθn hC2 hH1
              (Nat.mem_divisors.mp hM).1 hCrad hlog hlog2)
      _ = (C.divisors.card : ℝ) * (((((n * 10 ^ (n - 1) * 3 ^ n + 10 ^ n : ℕ)) : ℝ)) * (H : ℝ) ^ n) := by
          rw [Finset.sum_const, nsmul_eq_mul]
  refine le_trans hsum ?_
  have hcard := Commons.NumberTheory.Nat.card_divisors_le_two_pow_card_primeFactors C hCsq
  have hcard' : (C.divisors.card : ℝ) ≤ (2 : ℝ) ^ C.primeFactors.card := by
    calc (C.divisors.card : ℝ) ≤ (((2 ^ C.primeFactors.card : ℕ)) : ℝ) := by exact_mod_cast hcard
      _ = (2 : ℝ) ^ C.primeFactors.card := Nat.cast_pow 2 _
  have hB1n : (1 : ℕ) ≤ (n * 10 ^ (n - 1) * 3 ^ n + 10 ^ n : ℕ) := by
    have h : (1 : ℕ) ≤ 10 ^ n := Nat.one_le_pow n 10 (by norm_num)
    omega
  have hB1 : (1 : ℝ) ≤ ((((n * 10 ^ (n - 1) * 3 ^ n + 10 ^ n : ℕ)) : ℝ)) := by
    exact_mod_cast hB1n
  have homega : 1 ≤ C.primeFactors.card := by
    obtain ⟨q, hq⟩ := Nat.exists_prime_and_dvd (by omega : C ≠ 1)
    exact Finset.card_pos.mpr ⟨q, Nat.mem_primeFactors.mpr ⟨hq.1, hq.2, by omega⟩⟩
  calc (C.divisors.card : ℝ) * (((((n * 10 ^ (n - 1) * 3 ^ n + 10 ^ n : ℕ)) : ℝ)) * (H : ℝ) ^ n)
      ≤ (2 : ℝ) ^ C.primeFactors.card
          * (((((n * 10 ^ (n - 1) * 3 ^ n + 10 ^ n : ℕ)) : ℝ)) * (H : ℝ) ^ n) :=
        mul_le_mul_of_nonneg_right hcard' (by positivity)
    _ ≤ (((2 * (n * 10 ^ (n - 1) * 3 ^ n + 10 ^ n) : ℕ)) : ℝ) ^ C.primeFactors.card
          * (H : ℝ) ^ n := by
        have h2b : (2 : ℝ) ≤ (((2 * (n * 10 ^ (n - 1) * 3 ^ n + 10 ^ n) : ℕ)) : ℝ) := by
          have h3 : (2 : ℕ) ≤ (2 * (n * 10 ^ (n - 1) * 3 ^ n + 10 ^ n) : ℕ) := by omega
          exact_mod_cast h3
        have h2 : (2 : ℝ) ^ C.primeFactors.card
            ≤ (((2 * (n * 10 ^ (n - 1) * 3 ^ n + 10 ^ n) : ℕ)) : ℝ) ^ C.primeFactors.card :=
          pow_le_pow_left₀ (by norm_num) h2b _
        have hBp : ((((n * 10 ^ (n - 1) * 3 ^ n + 10 ^ n : ℕ)) : ℝ))
            ≤ ((((n * 10 ^ (n - 1) * 3 ^ n + 10 ^ n : ℕ)) : ℝ)) ^ C.primeFactors.card := by
          calc ((((n * 10 ^ (n - 1) * 3 ^ n + 10 ^ n : ℕ)) : ℝ))
              = ((((n * 10 ^ (n - 1) * 3 ^ n + 10 ^ n : ℕ)) : ℝ)) ^ 1 := (pow_one _).symm
            _ ≤ ((((n * 10 ^ (n - 1) * 3 ^ n + 10 ^ n : ℕ)) : ℝ)) ^ C.primeFactors.card :=
                pow_le_pow_right₀ hB1 homega
        calc (2 : ℝ) ^ C.primeFactors.card
              * (((((n * 10 ^ (n - 1) * 3 ^ n + 10 ^ n : ℕ)) : ℝ)) * (H : ℝ) ^ n)
            = ((2 : ℝ) ^ C.primeFactors.card
                * ((((n * 10 ^ (n - 1) * 3 ^ n + 10 ^ n : ℕ)) : ℝ))) * (H : ℝ) ^ n := by ring
          _ ≤ ((((2 * (n * 10 ^ (n - 1) * 3 ^ n + 10 ^ n) : ℕ)) : ℝ) ^ C.primeFactors.card)
                * (H : ℝ) ^ n := by
              refine mul_le_mul_of_nonneg_right ?_ (by positivity)
              calc (2 : ℝ) ^ C.primeFactors.card
                    * ((((n * 10 ^ (n - 1) * 3 ^ n + 10 ^ n : ℕ)) : ℝ))
                  ≤ (2 : ℝ) ^ C.primeFactors.card
                    * ((((n * 10 ^ (n - 1) * 3 ^ n + 10 ^ n : ℕ)) : ℝ)) ^ C.primeFactors.card :=
                    mul_le_mul_of_nonneg_left hBp (by positivity)
                _ = ((2 : ℝ) * ((((n * 10 ^ (n - 1) * 3 ^ n + 10 ^ n : ℕ)) : ℝ))) ^ C.primeFactors.card :=
                    (mul_pow _ _ _).symm
                _ = (((2 * (n * 10 ^ (n - 1) * 3 ^ n + 10 ^ n) : ℕ)) : ℝ) ^ C.primeFactors.card := by
                    push_cast
                    ring

end
end Submission.Vdw
