import Mathlib
import Submission.Work.BMF.Psi1_local_defs
import Submission.Work.BMF.dyadic_prime_card_le

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Chebyshev-type bound for the number of primes in a dyadic block

`Work.BMF.blkCount k` counts the primes in the log-dyadic block `(2^(k-1), 2^k]`.
This file proves `Work.BMF.block_prime_count`: there is a constant `C > 0` with
`blkCount k ≤ C * 2^k / k` for all `k ≥ 1`.

The proof uses the Chebyshev-type estimate `Work.BMF.dyadic_prime_card_le`, which bounds the
number of primes in `(⌊P⌋₊, ⌊2P⌋₊]` by `C P / log P`, applied with `P = 2^(k-1)`:
the block `(2^(k-1), 2^k]` has at most `C * 2^(k-1) / ((k-1) log 2)` primes.  Since
`k ≤ 2 (k-1)` for `k ≥ 2`, this is at most `C' * 2^k / k`; the case `k = 1` is the single
prime `2`.
-/

namespace Work.BMF

open Nat hiding log
open Finset Real
open scoped Nat.Prime

theorem block_prime_count :
    ∃ C : ℝ, 0 < C ∧ ∀ k : ℕ, 1 ≤ k →
      Work.BMF.blkCount k ≤ C * (2 : ℝ) ^ k / (k : ℝ) := by
  obtain ⟨C0, hC0pos, hC0⟩ := Work.BMF.dyadic_prime_card_le
  have hL : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨C0 / Real.log 2 + 1, by positivity, ?_⟩
  intro k hk
  rcases eq_or_lt_of_le hk with h1 | h2
  · -- `k = 1`: the block `(1, 2]` contains only the prime `2`.
    rw [← h1]
    have hb1 : Work.BMF.blkCount 1 = 1 := by
      rw [Work.BMF.blkCount]
      have h : (((Finset.Ioc (2 ^ (1 - 1)) (2 ^ 1)).filter Nat.Prime).card : ℕ) = 1 := by
        decide
      rw [h]; norm_num
    rw [hb1]
    have hpos : (0 : ℝ) < C0 / Real.log 2 := div_pos hC0pos hL
    nlinarith [hpos]
  · -- `k ≥ 2`: apply the dyadic prime-counting bound with `P = 2^(k-1)`.
    have hk2 : 2 ≤ k := h2
    have hPge : (2 : ℝ) ≤ (2 : ℝ) ^ (k - 1) := by
      have h1 : (1 : ℕ) ≤ k - 1 := by omega
      calc (2 : ℝ) = (2 : ℝ) ^ 1 := by norm_num
        _ ≤ (2 : ℝ) ^ (k - 1) := pow_le_pow_right₀ (by norm_num) h1
    have hfloorP : ⌊(2 : ℝ) ^ (k - 1)⌋₊ = 2 ^ (k - 1) := by
      have hc : (2 : ℝ) ^ (k - 1) = ((2 ^ (k - 1) : ℕ) : ℝ) := by push_cast; ring
      rw [hc, Nat.floor_natCast]
    have hfloor2P : ⌊2 * (2 : ℝ) ^ (k - 1)⌋₊ = 2 ^ k := by
      have h2k : 2 * (2 : ℝ) ^ (k - 1) = (2 : ℝ) ^ k := by
        rw [mul_comm, ← pow_succ, Nat.sub_add_cancel hk]
      have hc : 2 * (2 : ℝ) ^ (k - 1) = ((2 ^ k : ℕ) : ℝ) := by rw [h2k]; push_cast; ring
      rw [hc, Nat.floor_natCast]
    have hdyad : Work.BMF.blkCount k ≤
        C0 * (2 : ℝ) ^ (k - 1) / (((k - 1 : ℕ) : ℝ) * Real.log 2) := by
      have h := hC0 ((2 : ℝ) ^ (k - 1)) hPge
      rw [hfloorP, hfloor2P, Real.log_pow] at h
      simpa only [Work.BMF.blkCount] using h
    have hX : (0 : ℝ) < (2 : ℝ) ^ (k - 1) := by positivity
    have hkcast : ((k - 1 : ℕ) : ℝ) = (k : ℝ) - 1 := by rw [Nat.cast_sub hk]; norm_num
    have hkR2 : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk2
    have hkRpos : (0 : ℝ) < (k : ℝ) := by linarith
    have hkm1pos : (0 : ℝ) < (k : ℝ) - 1 := by linarith
    -- `k ≤ 2 (k-1)` and `C0 ≤ C0 + log 2` give the key numerical inequality.
    have key : C0 * (k : ℝ) ≤ 2 * (C0 + Real.log 2) * ((k : ℝ) - 1) := by
      have hkle : (k : ℝ) ≤ 2 * ((k : ℝ) - 1) := by linarith
      have hkm1 : (0 : ℝ) ≤ (k : ℝ) - 1 := le_of_lt hkm1pos
      have hCL : C0 ≤ C0 + Real.log 2 := by linarith
      nlinarith [hC0pos, hkle, hkm1, hCL]
    have h2k : 2 * (2 : ℝ) ^ (k - 1) = (2 : ℝ) ^ k := by
      rw [mul_comm, ← pow_succ, Nat.sub_add_cancel hk]
    have hRHS : (C0 / Real.log 2 + 1) * (2 : ℝ) ^ k / (k : ℝ) =
        (C0 + Real.log 2) * (2 : ℝ) ^ k / ((k : ℝ) * Real.log 2) := by
      field_simp
    have hstep : C0 * (2 : ℝ) ^ (k - 1) / (((k - 1 : ℕ) : ℝ) * Real.log 2) ≤
        (C0 / Real.log 2 + 1) * (2 : ℝ) ^ k / (k : ℝ) := by
      have hd1 : (0 : ℝ) < ((k : ℝ) - 1) * Real.log 2 := by positivity
      have hd2 : (0 : ℝ) < (k : ℝ) * Real.log 2 := by positivity
      rw [hRHS, hkcast, div_le_div_iff₀ hd1 hd2]
      rw [← h2k]
      have hexp := mul_le_mul_of_nonneg_right key
        (by positivity : (0 : ℝ) ≤ (2 : ℝ) ^ (k - 1) * Real.log 2)
      nlinarith [hexp]
    exact le_trans hdyad hstep

end Work.BMF
