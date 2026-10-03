import Mathlib
import Submission.Commons.NumberTheory.ArithmeticFunction.sum_tau_pow_div_le_logpow_explicit

namespace Commons.NumberTheory.Divisors

open Finset

theorem sum_tau_pow_div_le (k : ℕ) : ∃ C : ℝ, 0 < C ∧ ∀ y : ℕ, 1 ≤ y →
    ∑ d ∈ Finset.Icc 1 y, ((d.divisors.card : ℝ) ^ k) / (d : ℝ)
      ≤ C * (Real.log ((y : ℝ) + 2)) ^ (2 ^ k) := by
  obtain ⟨C, hCpos, hC⟩ :=
    Commons.NumberTheory.ArithmeticFunction.sum_tau_pow_div_le_logpow_explicit k
  refine ⟨max C 1, lt_max_of_lt_left hCpos, ?_⟩
  have hlog3 : (1 : ℝ) ≤ Real.log 3 := by
    have h := Real.log_le_log (Real.exp_pos 1) (le_of_lt Real.exp_one_lt_three)
    rwa [Real.log_exp] at h
  intro y hy
  rcases eq_or_lt_of_le hy with h1 | hy2
  · -- y = 1
    obtain rfl : y = 1 := h1.symm
    have hlhs : (∑ d ∈ Finset.Icc (1:ℕ) 1, ((d.divisors.card : ℝ) ^ k) / (d : ℝ)) = 1 := by
      simp
    rw [hlhs]
    have hbase : (1 : ℝ) ≤ Real.log (((1 : ℕ) : ℝ) + 2) := by
      have hc : (((1 : ℕ) : ℝ) + 2) = 3 := by norm_num
      rw [hc]; exact hlog3
    have h1le : (1 : ℝ) ≤ max C 1 := le_max_right C 1
    have hpow : (1 : ℝ) ≤ (Real.log (((1 : ℕ) : ℝ) + 2)) ^ (2 ^ k) := one_le_pow₀ hbase
    calc (1 : ℝ) = 1 * 1 := by ring
      _ ≤ max C 1 * (Real.log (((1 : ℕ) : ℝ) + 2)) ^ (2 ^ k) :=
          mul_le_mul h1le hpow zero_le_one (le_trans zero_le_one h1le)
  · -- y ≥ 2
    have h := hC y (by omega)
    have hypos : (0 : ℝ) < (y : ℝ) := by exact_mod_cast (by omega : 0 < y)
    have hlogy_nonneg : 0 ≤ Real.log (y : ℝ) :=
      Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ y))
    have hlogle : Real.log (y : ℝ) ≤ Real.log ((y : ℝ) + 2) := by
      apply Real.log_le_log hypos
      linarith
    have hpow_eq : (Real.log (y : ℝ)) ^ ((2 : ℝ) ^ k) = (Real.log (y : ℝ)) ^ (2 ^ k) := by
      rw [show ((2 : ℝ) ^ k) = ((2 ^ k : ℕ) : ℝ) by push_cast; ring, Real.rpow_natCast]
    have hmono : (Real.log (y : ℝ)) ^ (2 ^ k) ≤ (Real.log ((y : ℝ) + 2)) ^ (2 ^ k) :=
      pow_le_pow_left₀ hlogy_nonneg hlogle (2 ^ k)
    have hCle : C ≤ max C 1 := le_max_left C 1
    calc (∑ d ∈ Finset.Icc 1 y, ((d.divisors.card : ℝ) ^ k) / (d : ℝ))
        ≤ C * (Real.log (y : ℝ)) ^ ((2 : ℝ) ^ k) := h
      _ = C * (Real.log (y : ℝ)) ^ (2 ^ k) := by rw [hpow_eq]
      _ ≤ max C 1 * (Real.log ((y : ℝ) + 2)) ^ (2 ^ k) :=
          mul_le_mul hCle hmono (pow_nonneg hlogy_nonneg _)
            (le_trans (le_of_lt hCpos) hCle)

end Commons.NumberTheory.Divisors
