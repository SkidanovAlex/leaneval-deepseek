import Mathlib
import Submission.Commons.NumberTheory.ArithmeticFunction.tsum_vonMangoldt_rpow_neg_le
import Submission.Commons.NumberTheory.DirichletCharacter.completedLogDeriv_two_tight

open Complex DirichletCharacter ArithmeticFunction
open scoped Real LSeries.notation
set_option autoImplicit false
noncomputable section

namespace Commons.NumberTheory.DirichletCharacter

/-!
# Pointwise bound for the logarithmic derivative of a Dirichlet L-function

For `Re s ≥ 3/2` and any Dirichlet character `χ mod N`, the logarithmic derivative of the
Dirichlet L-function is bounded by `20`:

    ‖logDeriv (LFunction χ) s‖ ≤ 20.

For `Re s > 1` the logarithmic derivative is the negative of the L-series of the von
Mangoldt function twisted by `χ` (`DirichletCharacter.LSeries_twist_vonMangoldt_eq`), so its
absolute value is at most `∑' n, Λ n · n ^ (-σ)`, which is `≤ 20` for `σ ≥ 3/2`
(`Commons.NumberTheory.ArithmeticFunction.tsum_vonMangoldt_rpow_neg_le`).
-/

/-- The von Mangoldt series `∑' n, Λ n · n ^ (-σ)` is summable for `σ ≥ 3/2`, by comparison
with the `p`-series `∑ n ^ (-5/4)` (using `Λ n ≤ log n ≤ 4 n ^ (1/4)`). -/
private lemma summable_vonMangoldt_rpow_neg {σ : ℝ} (hσ : (3 : ℝ) / 2 ≤ σ) :
    Summable (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-σ)) := by
  have hle : ∀ n : ℕ,
      (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-σ)
        ≤ 4 * (n : ℝ) ^ (-(5 : ℝ) / 4) := by
    intro n
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn
      have h0Λ : (ArithmeticFunction.vonMangoldt 0 : ℝ) = 0 := by
        rw [ArithmeticFunction.vonMangoldt_apply]
        split_ifs with h
        · exact absurd h not_isPrimePow_zero
        · rfl
      rw [h0Λ, Nat.cast_zero, Real.zero_rpow (by linarith : (-σ) ≠ 0),
          Real.zero_rpow (by norm_num : (-(5 : ℝ) / 4) ≠ 0)]
      norm_num
    · have hnpos : 0 < (n : ℝ) := by exact_mod_cast hn
      have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      have hlog : Real.log (n : ℝ) ≤ 4 * (n : ℝ) ^ ((1 : ℝ) / 4) := by
        have h := Real.log_le_rpow_div (x := (n : ℝ)) (ε := (1 : ℝ) / 4)
          (Nat.cast_nonneg n) (by norm_num)
        rw [div_eq_mul_inv, show (((1 : ℝ) / 4 : ℝ)⁻¹) = 4 by norm_num, mul_comm] at h
        exact h
      calc (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-σ)
          ≤ Real.log (n : ℝ) * (n : ℝ) ^ (-σ) :=
            mul_le_mul_of_nonneg_right ArithmeticFunction.vonMangoldt_le_log
              (Real.rpow_nonneg (Nat.cast_nonneg n) _)
        _ ≤ (4 * (n : ℝ) ^ ((1 : ℝ) / 4)) * (n : ℝ) ^ (-σ) :=
            mul_le_mul_of_nonneg_right hlog (Real.rpow_nonneg (Nat.cast_nonneg n) _)
        _ = 4 * (n : ℝ) ^ ((1 : ℝ) / 4 - σ) := by
            rw [mul_assoc, ← Real.rpow_add hnpos]
            rw [show (1 : ℝ) / 4 + (-σ) = (1 : ℝ) / 4 - σ by ring]
        _ ≤ 4 * (n : ℝ) ^ (-(5 : ℝ) / 4) :=
            mul_le_mul_of_nonneg_left
              (Real.rpow_le_rpow_of_exponent_le hn1 (by linarith)) (by norm_num)
  exact Summable.of_nonneg_of_le
    (fun n => mul_nonneg ArithmeticFunction.vonMangoldt_nonneg
      (Real.rpow_nonneg (Nat.cast_nonneg n) _))
    hle ((Real.summable_nat_rpow.mpr (by norm_num : (-(5 : ℝ) / 4) < -1)).mul_left 4)

theorem logDeriv_LFunction_norm_le_re_ge_three_halves {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) {s : ℂ} (hs : (3 : ℝ) / 2 ≤ s.re) :
    ‖logDeriv (DirichletCharacter.LFunction χ) s‖ ≤ 20 := by
  have hs1 : 1 < s.re := by linarith
  rw [logDeriv_LFunction_eq_neg_twist χ hs1, norm_neg]
  have hsum : LSeriesSummable (↗χ * ↗Λ) s :=
    DirichletCharacter.LSeriesSummable_twist_vonMangoldt χ hs1
  have hsumN : Summable (fun n : ℕ => ‖LSeries.term (↗χ * ↗Λ) s n‖) :=
    summable_norm_iff.mpr hsum
  have hle1 : ‖L (↗χ * ↗Λ) s‖ ≤ ∑' n : ℕ, ‖LSeries.term (↗χ * ↗Λ) s n‖ :=
    norm_tsum_le_tsum_norm hsumN
  have hbound : ∀ n : ℕ, ‖LSeries.term (↗χ * ↗Λ) s n‖ ≤
      (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-s.re) := by
    intro n
    rcases eq_or_ne n 0 with hn0 | hn0
    · subst hn0
      simp [LSeries.term_zero]
    · rw [LSeries.norm_term_eq]
      simp only [hn0, if_false]
      have hnormχ : ‖(χ (n : ZMod N) : ℂ)‖ ≤ 1 := DirichletCharacter.norm_le_one χ _
      have hΛnonneg : (0 : ℝ) ≤ ArithmeticFunction.vonMangoldt n :=
        ArithmeticFunction.vonMangoldt_nonneg
      have hmul : ‖(χ (n : ZMod N) : ℂ) * ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ)‖
          ≤ (ArithmeticFunction.vonMangoldt n : ℝ) := by
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hΛnonneg]
        calc ‖(χ (n : ZMod N) : ℂ)‖ * ArithmeticFunction.vonMangoldt n
            ≤ 1 * ArithmeticFunction.vonMangoldt n :=
              mul_le_mul_of_nonneg_right hnormχ hΛnonneg
          _ = ArithmeticFunction.vonMangoldt n := one_mul _
      have hpow : (0 : ℝ) ≤ (n : ℝ) ^ s.re := Real.rpow_nonneg (Nat.cast_nonneg n) _
      calc ‖(χ (n : ZMod N) : ℂ) * ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ)‖
              / (n : ℝ) ^ s.re
          ≤ (ArithmeticFunction.vonMangoldt n : ℝ) / (n : ℝ) ^ s.re :=
            div_le_div_of_nonneg_right hmul hpow
        _ = (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-s.re) := by
            rw [Real.rpow_neg (Nat.cast_nonneg n), div_eq_mul_inv]
  have hsumg : Summable (fun n : ℕ =>
      (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-s.re)) :=
    summable_vonMangoldt_rpow_neg hs
  have hle2 : ∑' n : ℕ, ‖LSeries.term (↗χ * ↗Λ) s n‖
      ≤ ∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-s.re) :=
    Summable.tsum_le_tsum hbound hsumN hsumg
  have hle3 : ∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-s.re) ≤ 20 :=
    ArithmeticFunction.tsum_vonMangoldt_rpow_neg_le hs
  linarith

end Commons.NumberTheory.DirichletCharacter
