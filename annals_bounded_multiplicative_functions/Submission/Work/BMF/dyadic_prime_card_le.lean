import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

open Nat hiding log
open Finset Real
open scoped Nat.Prime

namespace Work.BMF

/-- The number of primes in the dyadic interval `(⌊P⌋₊, ⌊2P⌋₊]` is `O(P / log P)`.

This is a weak (but sufficient) upper bound: the count is at most `π ⌊2P⌋₊`, and Chebyshev's
explicit bound `Chebyshev.pi_le_log4_mul_div` gives
`π ⌊x⌋₊ ≤ log 4 * x / log √x + √x`.  Taking `x = 2P` and using `log √(2P) = log (2P) / 2`
together with `√(2P) ≤ 4P / log (2P)` (from `log y ≤ 2√y`) yields the constant
`C = 4 log 4 + 4`. -/
theorem dyadic_prime_card_le :
    ∃ C : ℝ, 0 < C ∧ ∀ P : ℝ, 2 ≤ P →
      (((Finset.Ioc ⌊P⌋₊ ⌊2 * P⌋₊).filter Nat.Prime).card : ℝ) ≤
        C * P / Real.log P := by
  refine ⟨4 * Real.log 4 + 4, ?_, ?_⟩
  · have h : 0 < Real.log 4 := Real.log_pos (by norm_num : (1:ℝ) < 4)
    linarith
  · intro P hP
    have hP0 : 0 < P := by linarith
    have h2P : 1 < 2 * P := by linarith
    have hsubset : (Finset.Ioc ⌊P⌋₊ ⌊2 * P⌋₊).filter Nat.Prime ⊆ (⌊2 * P⌋₊).primesLE := by
      intro p hp
      rw [Finset.mem_filter] at hp
      rw [Nat.mem_primesLE]
      exact ⟨(Finset.mem_Ioc.mp hp.1).2, hp.2⟩
    have hcard : ((Finset.Ioc ⌊P⌋₊ ⌊2 * P⌋₊).filter Nat.Prime).card ≤
        (⌊2 * P⌋₊).primeCounting := by
      calc ((Finset.Ioc ⌊P⌋₊ ⌊2 * P⌋₊).filter Nat.Prime).card
          ≤ (⌊2 * P⌋₊).primesLE.card := Finset.card_le_card hsubset
        _ = (⌊2 * P⌋₊).primeCounting := Nat.primesLE_card_eq_primeCounting _
    have hcardR : (((Finset.Ioc ⌊P⌋₊ ⌊2 * P⌋₊).filter Nat.Prime).card : ℝ) ≤
        ((⌊2 * P⌋₊).primeCounting : ℝ) := by
      exact_mod_cast hcard
    have hcheb := Chebyshev.pi_le_log4_mul_div h2P
    have hL : 0 < Real.log P := Real.log_pos (by linarith)
    have hM : 0 < Real.log (2 * P) := Real.log_pos h2P
    have hLM : Real.log P ≤ Real.log (2 * P) := Real.log_le_log hP0 (by linarith)
    have hAeq : Real.log 4 * (2 * P) / Real.log (Real.sqrt (2 * P)) =
        4 * Real.log 4 * P / Real.log (2 * P) := by
      rw [Real.log_sqrt (by linarith : (0:ℝ) ≤ 2 * P)]
      field_simp
      ring
    have hA : Real.log 4 * (2 * P) / Real.log (Real.sqrt (2 * P)) ≤
        4 * Real.log 4 * P / Real.log P := by
      rw [hAeq]
      exact div_le_div_of_nonneg_left (by positivity) hL hLM
    have h1 : Real.log (2 * P) ≤ 2 * Real.sqrt (2 * P) := by
      have h := Real.log_le_rpow_div (show (0:ℝ) ≤ 2 * P by linarith)
        (show (0:ℝ) < 1/2 by norm_num)
      have h' : (2 * P) ^ ((1:ℝ)/2) / (1/2) = 2 * Real.sqrt (2 * P) := by
        rw [← Real.sqrt_eq_rpow]; ring
      rw [h'] at h
      exact h
    have h2 : Real.sqrt (2 * P) * Real.log (2 * P) ≤ 4 * P := by
      have hsq : 0 ≤ Real.sqrt (2 * P) := Real.sqrt_nonneg _
      calc Real.sqrt (2 * P) * Real.log (2 * P)
            ≤ Real.sqrt (2 * P) * (2 * Real.sqrt (2 * P)) :=
              mul_le_mul_of_nonneg_left h1 hsq
        _ = 2 * (Real.sqrt (2 * P)) ^ 2 := by ring
        _ = 2 * (2 * P) := by rw [Real.sq_sqrt (by linarith : (0:ℝ) ≤ 2 * P)]
        _ = 4 * P := by ring
    have hB : Real.sqrt (2 * P) ≤ 4 * P / Real.log P := by
      have h3 : Real.sqrt (2 * P) ≤ 4 * P / Real.log (2 * P) := by
        rw [le_div_iff₀ hM]
        exact h2
      calc Real.sqrt (2 * P) ≤ 4 * P / Real.log (2 * P) := h3
        _ ≤ 4 * P / Real.log P := div_le_div_of_nonneg_left (by positivity) hL hLM
    calc (((Finset.Ioc ⌊P⌋₊ ⌊2 * P⌋₊).filter Nat.Prime).card : ℝ)
        ≤ ((⌊2 * P⌋₊).primeCounting : ℝ) := hcardR
      _ ≤ Real.log 4 * (2 * P) / Real.log (Real.sqrt (2 * P)) + Real.sqrt (2 * P) := hcheb
      _ ≤ (4 * Real.log 4 + 4) * P / Real.log P := by
          calc Real.log 4 * (2 * P) / Real.log (Real.sqrt (2 * P)) + Real.sqrt (2 * P)
              ≤ 4 * Real.log 4 * P / Real.log P + 4 * P / Real.log P := add_le_add hA hB
            _ = (4 * Real.log 4 + 4) * P / Real.log P := by ring

end Work.BMF
