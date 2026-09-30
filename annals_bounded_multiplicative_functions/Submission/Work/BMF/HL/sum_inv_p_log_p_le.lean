import Mathlib
import Submission.Work.BMF.HL.prime_block_inv_log_le

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF.HL

open Finset Real

/-- Telescoping the block estimate `Σ_{a<p≤a²} 1/(p log p) ≤ (log 2 + C)/log a` along the tower
`a, a², a⁴, …, a^(2^K)`: block `k` contributes at most `(log 2 + C)/(2^k log a)`, and the geometric
series gives the stated bound. -/
private lemma iter_bound_aux (C : ℝ)
    (hblk : ∀ x : ℝ, 11 ≤ x →
      (∑ p ∈ (⌊x ^ 2⌋₊).primesLE \ (⌊x⌋₊).primesLE, 1 / ((p : ℝ) * Real.log p))
        ≤ (Real.log 2 + C) / Real.log x)
    (a : ℝ) (ha : 11 ≤ a) (K : ℕ) :
    (∑ p ∈ (⌊a ^ (2 ^ K)⌋₊).primesLE \ (⌊a⌋₊).primesLE, 1 / ((p : ℝ) * Real.log p))
      ≤ 2 * (Real.log 2 + C) * (1 - (1 / 2 : ℝ) ^ K) / Real.log a := by
  have ha1 : (1 : ℝ) < a := by linarith
  have hlogapos : 0 < Real.log a := Real.log_pos ha1
  induction K with
  | zero => simp
  | succ K ih =>
    have hpow : a ^ (2 ^ (K + 1)) = (a ^ (2 ^ K)) ^ 2 := by
      rw [Nat.pow_succ, ← pow_mul]
    rw [hpow]
    have hle1 : a ≤ a ^ (2 ^ K) := by
      simpa using pow_le_pow_right₀ (le_of_lt ha1) (one_le_pow₀ (by norm_num : (1:ℕ) ≤ 2))
    have hx1 : (1 : ℝ) ≤ a ^ (2 ^ K) := le_trans (le_of_lt ha1) hle1
    have hx11 : (11 : ℝ) ≤ a ^ (2 ^ K) := le_trans ha hle1
    have hle2 : a ^ (2 ^ K) ≤ (a ^ (2 ^ K)) ^ 2 := by
      simpa using pow_le_pow_right₀ hx1 (show (1 : ℕ) ≤ 2 by norm_num)
    have hAX : ⌊a⌋₊ ≤ ⌊a ^ (2 ^ K)⌋₊ := Nat.floor_mono hle1
    have hXY : ⌊a ^ (2 ^ K)⌋₊ ≤ ⌊(a ^ (2 ^ K)) ^ 2⌋₊ := Nat.floor_mono hle2
    have h1 := Finset.sum_sdiff (Nat.primesLE_mono hAX)
      (f := fun p : ℕ => 1 / ((p : ℝ) * Real.log p))
    have h2 := Finset.sum_sdiff (Nat.primesLE_mono (le_trans hAX hXY))
      (f := fun p : ℕ => 1 / ((p : ℝ) * Real.log p))
    have h3 := Finset.sum_sdiff (Nat.primesLE_mono hXY)
      (f := fun p : ℕ => 1 / ((p : ℝ) * Real.log p))
    have hsplit : (∑ p ∈ (⌊(a ^ (2 ^ K)) ^ 2⌋₊).primesLE \ (⌊a⌋₊).primesLE,
          1 / ((p : ℝ) * Real.log p))
        = (∑ p ∈ (⌊(a ^ (2 ^ K)) ^ 2⌋₊).primesLE \ (⌊a ^ (2 ^ K)⌋₊).primesLE,
            1 / ((p : ℝ) * Real.log p))
          + (∑ p ∈ (⌊a ^ (2 ^ K)⌋₊).primesLE \ (⌊a⌋₊).primesLE,
              1 / ((p : ℝ) * Real.log p)) := by
      linarith
    have hblock := hblk (a ^ (2 ^ K)) hx11
    have hlogpow : Real.log (a ^ (2 ^ K)) = (2 : ℝ) ^ K * Real.log a := by
      rw [Real.log_pow]
      push_cast
      ring
    rw [hlogpow] at hblock
    have hmain : (∑ p ∈ (⌊(a ^ (2 ^ K)) ^ 2⌋₊).primesLE \ (⌊a⌋₊).primesLE,
          1 / ((p : ℝ) * Real.log p))
        ≤ (Real.log 2 + C) / ((2 : ℝ) ^ K * Real.log a)
          + 2 * (Real.log 2 + C) * (1 - (1 / 2 : ℝ) ^ K) / Real.log a := by
      rw [hsplit]
      linarith [ih, hblock]
    have key : (Real.log 2 + C) / ((2 : ℝ) ^ K * Real.log a)
          + 2 * (Real.log 2 + C) * (1 - (1 / 2 : ℝ) ^ K) / Real.log a
        = 2 * (Real.log 2 + C) * (1 - (1 / 2 : ℝ) ^ (K + 1)) / Real.log a := by
      have hK : (1 / 2 : ℝ) ^ K = 1 / (2 : ℝ) ^ K := by rw [div_pow, one_pow]
      have hK1 : (1 / 2 : ℝ) ^ (K + 1) = 1 / (2 : ℝ) ^ (K + 1) := by rw [div_pow, one_pow]
      have h2p : (2 : ℝ) ^ (K + 1) = (2 : ℝ) ^ K * 2 := by rw [pow_succ]
      rw [hK, hK1, h2p]
      have ht : ((2 : ℝ) ^ K) ≠ 0 := by positivity
      have hL : Real.log a ≠ 0 := ne_of_gt hlogapos
      field_simp
      ring
    linarith [hmain, key]

/-- Sharp Mertens-type bound: `Σ_{a < p ≤ b} 1/(p log p) ≤ C / log a` for `11 ≤ a ≤ b`, with an
absolute constant `C`.  (In the continuum this sum is `∫_a^b dt/(t log²t) = 1/log a − 1/log b`,
so `C = 2` has slack.)  Beware: for every fixed `ε > 0` the bound `C_ε/log^{1−ε} a` is *not*
enough for the intended application — the exact `1/log a` rate is essential. -/
theorem sum_inv_p_log_p_le :
    ∃ C : ℝ, 0 < C ∧ ∀ a b : ℝ, 11 ≤ a → a ≤ b →
      (∑ p ∈ (⌊b⌋₊).primesLE \ (⌊a⌋₊).primesLE, 1 / ((p : ℝ) * Real.log p))
        ≤ C / Real.log a := by
  obtain ⟨C₀, hC₀pos, hblk⟩ := prime_block_inv_log_le
  refine ⟨2 * (Real.log 2 + C₀), by positivity, ?_⟩
  intro a b ha hab
  have ha1 : (1 : ℝ) < a := by linarith
  have hlogapos : 0 < Real.log a := Real.log_pos ha1
  have hBpos : 0 < Real.log 2 + C₀ := by
    have h := Real.log_pos (show (1 : ℝ) < 2 by norm_num)
    linarith
  -- pick a tower level `a^(2^n)` above `b`
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt b ha1
  have hle : b ≤ a ^ (2 ^ n) := by
    have h1 : (1 : ℝ) ≤ a := le_of_lt ha1
    have hn2 : n ≤ 2 ^ n := (Nat.lt_two_pow_self (n := n)).le
    exact le_trans (le_of_lt hn) (pow_le_pow_right₀ h1 hn2)
  -- monotonicity in the upper endpoint
  have hfloor : ⌊b⌋₊ ≤ ⌊a ^ (2 ^ n)⌋₊ := Nat.floor_mono hle
  have hsub : (⌊b⌋₊).primesLE \ (⌊a⌋₊).primesLE ⊆
      (⌊a ^ (2 ^ n)⌋₊).primesLE \ (⌊a⌋₊).primesLE := by
    intro p hp
    rw [Finset.mem_sdiff] at hp ⊢
    exact ⟨Nat.primesLE_mono hfloor hp.1, hp.2⟩
  have hnonneg : ∀ p ∈ (⌊a ^ (2 ^ n)⌋₊).primesLE \ (⌊a⌋₊).primesLE,
      p ∉ (⌊b⌋₊).primesLE \ (⌊a⌋₊).primesLE → (0 : ℝ) ≤ 1 / ((p : ℝ) * Real.log p) := by
    intro p hp _
    have hpp : p.Prime := Nat.prime_of_mem_primesLE (Finset.mem_sdiff.mp hp).1
    have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hpp.two_le
    have hlogp : 0 < Real.log p := Real.log_pos (by linarith)
    positivity
  have hmono := Finset.sum_le_sum_of_subset_of_nonneg hsub hnonneg
  calc (∑ p ∈ (⌊b⌋₊).primesLE \ (⌊a⌋₊).primesLE, 1 / ((p : ℝ) * Real.log p))
      ≤ (∑ p ∈ (⌊a ^ (2 ^ n)⌋₊).primesLE \ (⌊a⌋₊).primesLE,
          1 / ((p : ℝ) * Real.log p)) := hmono
    _ ≤ 2 * (Real.log 2 + C₀) * (1 - (1 / 2 : ℝ) ^ n) / Real.log a :=
        iter_bound_aux C₀ hblk a ha n
    _ ≤ 2 * (Real.log 2 + C₀) / Real.log a := by
        have hstep : 2 * (Real.log 2 + C₀) * (1 - (1 / 2 : ℝ) ^ n) / Real.log a
            = (2 * (Real.log 2 + C₀) / Real.log a) * (1 - (1 / 2 : ℝ) ^ n) := by ring
        rw [hstep]
        have hfac : (0:ℝ) ≤ 2 * (Real.log 2 + C₀) / Real.log a :=
          div_nonneg (by linarith) (le_of_lt hlogapos)
        exact mul_le_of_le_one_right hfac (by
          have h2 : (0:ℝ) ≤ (1/2)^n := pow_nonneg (by norm_num) n
          linarith)

end Work.BMF.HL
