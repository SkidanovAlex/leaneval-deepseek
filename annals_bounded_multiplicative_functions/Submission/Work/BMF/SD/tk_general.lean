import Mathlib
import Submission.Work.BMF.Defs
import Submission.Work.BMF.SD.tk_short

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# `Work.BMF.SD.tk_general`

The second-moment (large-sieve) bound for the discrepancy of `f` on arithmetic progressions
to prime moduli, with **no** restriction `H ≤ x`:

with `2 ≤ P ≤ Q`, `Q ^ 3 ≤ H`, `1 ≤ H`, `x ≥ 0` and `‖f n‖ ≤ 1`,

`Σ_{p ∈ primesIn P Q} p * ‖Σ_{m ∈ [x/p, (x+H)/p]} f (p*m) - (1/p) * Σ_{n ∈ [x, x+H]} f n‖ ^ 2
   ≤ 200 H^2`.

The two structural reductions `per_prime_sum_le` and `pair_large_sieve` (from
`Submission.Work.BMF.SD.tk_short`) hold for arbitrary `x, H`; the only place where the
short-interval hypothesis could have entered `tk_short` is the arithmetic bound on the length
`N = ⌊x + H⌋₊ + 1 - ⌈x⌉₊` of `natIcc x (x + H)`, and that bound `N ≤ H + 1` is in fact
unconditional. Hence the same final assembly applies.
-/

namespace Work.BMF.SD

open Finset Real Complex
open Work.BMF

theorem tk_general (P Q x H : ℝ) (f : ℕ → ℂ) (hP : 2 ≤ P) (hPQ : P ≤ Q)
    (hQ3 : Q ^ 3 ≤ H) (hH1 : 1 ≤ H) (hx : 0 ≤ x) (hf : ∀ n, ‖f n‖ ≤ 1) :
    (∑ p ∈ Work.BMF.primesIn P Q, (p : ℝ) *
      ‖(∑ m ∈ Work.BMF.natIcc (x / p) ((x + H) / p), f (p * m))
        - (1 / p) * (∑ n ∈ Work.BMF.natIcc x (x + H), f n)‖ ^ 2) ≤ 200 * H ^ 2 := by
  have hQpos : 0 < Q := by linarith
  have hHpos : 0 < H := by linarith
  -- the two structural reductions (valid for arbitrary `x`, `H`)
  refine (per_prime_sum_le P Q x H f).trans ?_
  refine (pair_large_sieve P Q x H f hP hPQ).trans ?_
  -- arithmetic: the interval length `N` is unconditionally at most `H + 1`
  set N : ℕ := ⌊x + H⌋₊ + 1 - ⌈x⌉₊ with hNdef
  have hSnn : 0 ≤ ∑ n ∈ Work.BMF.natIcc x (x + H), ‖f n‖ ^ 2 :=
    Finset.sum_nonneg (fun n _ => sq_nonneg _)
  have hN1 : ((N : ℕ) : ℝ) ≤ H + 1 := by
    rw [hNdef]
    rcases le_or_gt ⌈x⌉₊ (⌊x + H⌋₊ + 1) with h | h
    · rw [Nat.cast_sub h]
      have hfl : ((⌊x + H⌋₊ : ℕ) : ℝ) ≤ x + H :=
        Nat.floor_le (by linarith)
      have hce : x ≤ ((⌈x⌉₊ : ℕ) : ℝ) := Nat.le_ceil x
      push_cast
      linarith
    · have h0 : ⌊x + H⌋₊ + 1 - ⌈x⌉₊ = 0 := by omega
      rw [h0]; simp; linarith
  have hcard : (∑ n ∈ Work.BMF.natIcc x (x + H), ‖f n‖ ^ 2) ≤ (N : ℝ) := by
    have hterm : ∀ n, ‖f n‖ ^ 2 ≤ (1:ℝ) := by
      intro n; nlinarith [hf n, norm_nonneg (f n)]
    calc ∑ n ∈ Work.BMF.natIcc x (x + H), ‖f n‖ ^ 2
        ≤ ∑ n ∈ Work.BMF.natIcc x (x + H), (1:ℝ) := Finset.sum_le_sum (fun n _ => hterm n)
      _ = ((Work.BMF.natIcc x (x + H)).card : ℝ) := by simp
      _ = (N : ℝ) := by
          rw [hNdef, Work.BMF.natIcc, Nat.card_Icc]
  have hS1 : (∑ n ∈ Work.BMF.natIcc x (x + H), ‖f n‖ ^ 2) ≤ H + 1 := hcard.trans hN1
  -- bounds on the prefactor
  have hN2 : 2 * (N : ℝ) + 2 ≤ 6 * H := by linarith [hN1, hH1]
  have hlog : 2 + Real.log (2 * (N : ℝ) + 2) ≤ 10 * H ^ (1/3 : ℝ) := by
    have h1 : Real.log (2 * (N : ℝ) + 2) ≤ Real.log (6 * H) :=
      Real.log_le_log (by positivity) hN2
    have h2 : Real.log (6 * H) = Real.log 6 + Real.log H :=
      Real.log_mul (by norm_num) (by linarith)
    have h3 : Real.log 6 ≤ 5 := by
      have := Real.log_le_sub_one_of_pos (show (0:ℝ) < 6 by norm_num); linarith
    have h4 : Real.log H ≤ 3 * H ^ (1/3 : ℝ) := log_le_three_rpow H hH1
    have h5 : (1:ℝ) ≤ H ^ (1/3 : ℝ) := by
      have := Real.rpow_le_rpow (show (0:ℝ) ≤ 1 by norm_num) hH1
        (show (0:ℝ) ≤ (1/3 : ℝ) by norm_num)
      rwa [Real.one_rpow] at this
    linarith
  have hQle : Q ≤ H ^ (1/3 : ℝ) := by
    have h1 : (Q ^ 3 : ℝ) ^ (1/3 : ℝ) ≤ H ^ (1/3 : ℝ) :=
      Real.rpow_le_rpow (by positivity) hQ3 (by norm_num)
    have hpow : (Q ^ 3 : ℝ) ^ (1/3 : ℝ) = Q := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (le_of_lt hQpos)]
      rw [show (((3:ℕ):ℝ) * (1/3 : ℝ)) = 1 by norm_num, Real.rpow_one]
    rwa [hpow] at h1
  have hQ23 : Q ^ 2 ≤ H ^ (2/3 : ℝ) := sq_le_rpow_two_thirds (le_of_lt hQpos) hHpos hQle
  have hdelta : 8 / (1 / Q ^ 2) = 8 * Q ^ 2 := by
    field_simp
  have hb : (8 / (1 / Q ^ 2)) * (2 + Real.log (2 * (N : ℝ) + 2)) ≤ 80 * H := by
    rw [hdelta]
    calc 8 * Q ^ 2 * (2 + Real.log (2 * (N : ℝ) + 2))
        ≤ 8 * Q ^ 2 * (10 * H ^ (1/3 : ℝ)) := by
          apply mul_le_mul_of_nonneg_left hlog
          positivity
      _ = 80 * (Q ^ 2 * H ^ (1/3 : ℝ)) := by ring
      _ ≤ 80 * (H ^ (2/3 : ℝ) * H ^ (1/3 : ℝ)) := by
          apply mul_le_mul_of_nonneg_left _ (by norm_num)
          exact mul_le_mul_of_nonneg_right hQ23 (Real.rpow_nonneg (le_of_lt hHpos) _)
      _ = 80 * H := by
          rw [← Real.rpow_add hHpos, show (2/3:ℝ) + 1/3 = 1 by norm_num, Real.rpow_one]
  have hM : 2 * (N : ℝ) + (8 / (1 / Q ^ 2)) * (2 + Real.log (2 * (N : ℝ) + 2))
      ≤ 84 * H := by linarith [hN1, hb]
  calc (2 * (N : ℝ) + (8 / (1 / Q ^ 2)) * (2 + Real.log (2 * (N : ℝ) + 2)))
        * ∑ n ∈ Work.BMF.natIcc x (x + H), ‖f n‖ ^ 2
      ≤ (84 * H) * (H + 1) := by
        apply mul_le_mul hM hS1 hSnn (by positivity)
    _ = 84 * H * (H + 1) := by ring
    _ ≤ 168 * H ^ 2 := by nlinarith
    _ ≤ 200 * H ^ 2 := by nlinarith

end Work.BMF.SD
