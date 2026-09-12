import Mathlib
import Submission.RS
import Submission.Sec3H_defs

example (k : ℕ) : (1 / (2 : ℝ) ^ 10) ^ k = 1 / (2 : ℝ) ^ (10 * k) := by
  rw [one_div, inv_pow, ← pow_mul]
  ring

example (t k : ℕ) : ((2 : ℝ) ^ t / (2 : ℝ) ^ (t + 10)) ^ k = (1 / (2 : ℝ) ^ 10) ^ k := by
  have h : (2 : ℝ) ^ t / (2 : ℝ) ^ (t + 10) = 1 / (2 : ℝ) ^ 10 := by
    rw [show (2 : ℝ) ^ (t + 10) = (2 : ℝ) ^ t * (2 : ℝ) ^ 10 by rw [pow_add]]
    field_simp [show (2 : ℝ) ^ t ≠ 0 by positivity]
  rw [h]

example (k : ℕ) (hk : 1 ≤ k) : 1 / (2 : ℝ) ^ (10 * k) ≤ 1 / (2 : ℝ) ^ (9 * k) := by
  have hmono : (2 : ℝ) ^ (9 * k) ≤ (2 : ℝ) ^ (10 * k) := by
    exact pow_le_pow_right₀ (by norm_num) (by omega)
  have h1 : 0 < (2 : ℝ) ^ (9 * k) := by positivity
  exact (one_div_le_one_div_of_le h1 hmono)

-- scale · sqrt = 1
example (t : ℕ) : (Real.sqrt (2 ^ (t + 1) : ℝ))⁻¹ * Real.sqrt (2 ^ (t + 1) : ℝ) = 1 := by
  field_simp [show Real.sqrt (2 ^ (t + 1) : ℝ) ≠ 0 by positivity]

open Submission.Sec3H
-- norm of ((a:ℂ)⁻¹)^k * w
example (a : ℝ) (ha : 0 ≤ a) (k : ℕ) (w : ℂ) : ‖(((a : ℂ)⁻¹) ^ k) * w‖ = (a⁻¹) ^ k * ‖w‖ := by
  rw [norm_mul]
  have hpow : ‖((a : ℂ)⁻¹) ^ k‖ = (a⁻¹) ^ k := by
    rw [norm_pow]
    rw [norm_inv, norm_of_real, abs_of_nonneg ha]
  rw [hpow]

def TT (t : ℕ) : ℕ := 2 ^ (t + 10)
example (t : ℕ) : 0 < (TT t : ℝ) := by
  have h : 0 < 2 ^ (t + 10) := pow_pos (by norm_num) (t + 10)
  exact_mod_cast h
