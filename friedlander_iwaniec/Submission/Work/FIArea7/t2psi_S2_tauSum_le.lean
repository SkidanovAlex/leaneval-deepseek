import Mathlib
import Submission.Commons.NumberTheory.ArithmeticFunction.sum_tau_pow_div_le_logpow_explicit
import Submission.Commons.NumberTheory.DivisorBound.card_divisors_le_rpow
import Submission.Commons.NumberTheory.FriedlanderIwaniec.tau_le_nine_sum_divisors_cube

namespace Work.FIArea7

/-- The weighted divisor sum `∑_{a ≤ A} τ(a)^4 a^{-1/4} ≤ C A^{3/4} (log(A+2))^{16}`, obtained
from `∑_{a ≤ A} τ(a)^4 / a ≤ C (log A)^{2^4}` (`k = 4` in
`Submission.Commons.NumberTheory.ArithmeticFunction.sum_tau_pow_div_le_logpow_explicit`, already
imported by `Submission.Work.FIArea7.S2Imports`)
by `a^{-1/4} = a^{3/4} · a^{-1}`. -/
theorem t2psi_S2_tauSum_le :
    ∃ C : ℝ, 0 < C ∧ ∀ A : ℕ,
      (∑ a ∈ Finset.Icc 1 A,
          (((a.divisors.card : ℕ) : ℝ)) ^ 4 * (a : ℝ) ^ (-(1:ℝ)/4))
        ≤ C * (A : ℝ) ^ ((3:ℝ)/4) * (Real.log ((A : ℝ) + 2)) ^ 16 := by
  obtain ⟨C0, hC0pos, hC0⟩ :=
    Commons.NumberTheory.ArithmeticFunction.sum_tau_pow_div_le_logpow_explicit 4
  have hlog3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  refine ⟨max C0 ((Real.log 3)⁻¹ ^ 16 + 1), ?_, ?_⟩
  · exact lt_of_lt_of_le (by positivity) (le_max_right _ _)
  · intro A
    rcases Nat.lt_or_ge A 2 with hA | hA
    · interval_cases A
      · -- A = 0: the sum is empty and the right-hand side vanishes.
        simp [Real.zero_rpow (by norm_num : ((3:ℝ)/4) ≠ 0)]
      · -- A = 1: both sides are explicit, the constant is chosen large enough.
        have h3eq : ((1:ℝ)+2) = 3 := by norm_num
        have hlog' : 0 < Real.log ((1:ℝ)+2) := by rw [h3eq]; exact hlog3
        have hlog'ne : Real.log ((1:ℝ)+2) ≠ 0 := ne_of_gt hlog'
        have hCge : (Real.log ((1:ℝ)+2))⁻¹ ^ 16 ≤ max C0 ((Real.log 3)⁻¹ ^ 16 + 1) := by
          rw [h3eq]
          exact le_trans (le_add_of_nonneg_right zero_le_one) (le_max_right _ _)
        have hone : 1 ≤ max C0 ((Real.log 3)⁻¹ ^ 16 + 1) * (Real.log ((1:ℝ)+2)) ^ 16 := by
          have hinv : (Real.log ((1:ℝ)+2))⁻¹ ^ 16 = ((Real.log ((1:ℝ)+2)) ^ 16)⁻¹ := by
            rw [inv_pow]
          calc (1:ℝ) = ((Real.log ((1:ℝ)+2)) ^ 16)⁻¹ * (Real.log ((1:ℝ)+2)) ^ 16 :=
                (inv_mul_cancel₀ (pow_ne_zero 16 hlog'ne)).symm
            _ = (Real.log ((1:ℝ)+2))⁻¹ ^ 16 * (Real.log ((1:ℝ)+2)) ^ 16 := by rw [hinv]
            _ ≤ max C0 ((Real.log 3)⁻¹ ^ 16 + 1) * (Real.log ((1:ℝ)+2)) ^ 16 :=
                mul_le_mul_of_nonneg_right hCge (pow_nonneg hlog'.le 16)
        have hsum1 : (∑ a ∈ Finset.Icc (1:ℕ) 1,
            (((a.divisors.card : ℕ) : ℝ)) ^ 4 * (a : ℝ) ^ (-(1:ℝ)/4)) = (1:ℝ) := by
          rw [Finset.Icc_self, Finset.sum_singleton]
          norm_num [Real.one_rpow]
        rw [hsum1]
        simpa using hone
    · -- Main case `2 ≤ A`.
      have hA2R : (2:ℝ) ≤ (A:ℝ) := by exact_mod_cast hA
      have hApos : (0:ℝ) < (A:ℝ) := by linarith
      have hlogA_nn : 0 ≤ Real.log (A:ℝ) := Real.log_nonneg (by linarith)
      have hlog_mono : Real.log (A:ℝ) ≤ Real.log ((A:ℝ)+2) :=
        Real.log_le_log (by linarith) (by linarith)
      have hpow16 : (Real.log (A:ℝ))^16 ≤ (Real.log ((A:ℝ)+2))^16 :=
        pow_le_pow_left₀ hlogA_nn hlog_mono 16
      have hArpow_nn : 0 ≤ (A:ℝ)^((3:ℝ)/4) := Real.rpow_nonneg (le_of_lt hApos) _
      have hC0A : (∑ a ∈ Finset.Icc 1 A, (((a.divisors.card : ℕ) : ℝ)) ^ 4 / (a : ℝ))
          ≤ C0 * (Real.log (A:ℝ)) ^ 16 := by
        have h := hC0 A hA
        have heq : C0 * (Real.log (A:ℝ)) ^ ((2:ℝ)^4) = C0 * (Real.log (A:ℝ)) ^ (16:ℕ) := by
          norm_num
        rw [heq] at h
        exact h
      -- Pointwise: `τ(a)^4 · a^{-1/4} ≤ (τ(a)^4 / a) · A^{3/4}` for `1 ≤ a ≤ A`.
      have hterm : ∀ a ∈ Finset.Icc 1 A,
          ((((a.divisors.card : ℕ) : ℝ)) ^ 4 * (a : ℝ) ^ (-(1:ℝ)/4))
            ≤ ((((a.divisors.card : ℕ) : ℝ)) ^ 4 / (a : ℝ)) * (A : ℝ) ^ ((3:ℝ)/4) := by
        intro a ha
        have ha1 : 1 ≤ a := (Finset.mem_Icc.mp ha).1
        have haA : a ≤ A := (Finset.mem_Icc.mp ha).2
        have hapos : (0:ℝ) < (a:ℝ) := by exact_mod_cast (by omega : 0 < a)
        have haAR : (a:ℝ) ≤ (A:ℝ) := by exact_mod_cast haA
        have hrsplit : (a:ℝ)^((3:ℝ)/4) * (a:ℝ)⁻¹
            ≤ (A:ℝ)^((3:ℝ)/4) * (a:ℝ)⁻¹ :=
          mul_le_mul_of_nonneg_right
            (Real.rpow_le_rpow (le_of_lt hapos) haAR (by norm_num)) (by positivity)
        have hsplit : (a:ℝ)^(-(1:ℝ)/4) = (a:ℝ)^((3:ℝ)/4) * (a:ℝ)⁻¹ := by
          rw [show (-(1:ℝ)/4) = (3:ℝ)/4 + (-1) by norm_num, Real.rpow_add hapos,
            Real.rpow_neg_one]
        calc ((((a.divisors.card : ℕ) : ℝ)) ^ 4 * (a : ℝ) ^ (-(1:ℝ)/4))
            ≤ ((((a.divisors.card : ℕ) : ℝ)) ^ 4) * ((A:ℝ)^((3:ℝ)/4) * (a:ℝ)⁻¹) := by
              rw [hsplit]
              exact mul_le_mul_of_nonneg_left hrsplit (by positivity)
          _ = ((((a.divisors.card : ℕ) : ℝ)) ^ 4 / (a : ℝ)) * (A : ℝ) ^ ((3:ℝ)/4) := by
              rw [div_eq_mul_inv]; ring
      calc (∑ a ∈ Finset.Icc 1 A,
            (((a.divisors.card : ℕ) : ℝ)) ^ 4 * (a : ℝ) ^ (-(1:ℝ)/4))
          ≤ ∑ a ∈ Finset.Icc 1 A,
              ((((a.divisors.card : ℕ) : ℝ)) ^ 4 / (a : ℝ)) * (A : ℝ) ^ ((3:ℝ)/4) :=
            Finset.sum_le_sum hterm
        _ = (∑ a ∈ Finset.Icc 1 A, (((a.divisors.card : ℕ) : ℝ)) ^ 4 / (a : ℝ))
              * (A : ℝ) ^ ((3:ℝ)/4) := by
            rw [Finset.sum_mul]
        _ ≤ (C0 * (Real.log (A:ℝ)) ^ 16) * (A : ℝ) ^ ((3:ℝ)/4) :=
            mul_le_mul_of_nonneg_right hC0A hArpow_nn
        _ ≤ (max C0 ((Real.log 3)⁻¹ ^ 16 + 1) * (Real.log ((A:ℝ)+2)) ^ 16)
              * (A : ℝ) ^ ((3:ℝ)/4) := by
            apply mul_le_mul_of_nonneg_right _ hArpow_nn
            exact mul_le_mul (le_max_left _ _) hpow16 (by positivity)
              (le_trans hC0pos.le (le_max_left _ _))
        _ = max C0 ((Real.log 3)⁻¹ ^ 16 + 1) * (A : ℝ) ^ ((3:ℝ)/4)
              * (Real.log ((A:ℝ)+2)) ^ 16 := by
            ring

end Work.FIArea7
