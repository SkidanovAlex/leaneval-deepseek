import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Elementary real/natural-number inequalities used in the spread-hitting theorem

These are self-contained facts (no dependence on the rest of the development).
-/

open scoped BigOperators

set_option linter.unusedVariables false

namespace Submission
namespace Est

/-- `(1 + 1/n)^n ≤ 3` for `n ≥ 1`. -/
theorem one_add_inv_pow_le_three (n : ℕ) (hn : 1 ≤ n) :
    (1 + (1 : ℝ) / n) ^ n ≤ 3 := by
  calc
    (1 + (1 : ℝ) / n) ^ n = (1 + (n : ℝ)⁻¹) ^ n := by
      rw [one_div]
    _ ≤ Real.exp 1 := Real.one_add_inv_pow_le_exp (n := n)
    _ ≤ 3 := (Real.exp_one_lt_three).le

/-- A factorial lower bound: `(ℓ/3)^ℓ ≤ ℓ!` for ℓ ≥ 1 (equivalent: `3^ℓ · ℓ! ≥ ℓ^ℓ`). -/
theorem pow_le_three_pow_factorial (ℓ : ℕ) : (ℓ : ℝ) ^ ℓ ≤ 3 ^ ℓ * (ℓ.factorial : ℝ) := by
  induction ℓ with
  | zero =>
      norm_num
  | succ ℓ ih =>
      by_cases hℓz : ℓ = 0
      · subst ℓ
        norm_num
      · have hℓ1 : 1 ≤ ℓ := by omega
        have hℓR : (ℓ : ℝ) ≠ 0 := by exact_mod_cast hℓz
        have hdec : (↑(ℓ + 1 : ℕ) : ℝ) ^ ℓ =
            ((↑(ℓ + 1 : ℕ) : ℝ) / (ℓ : ℝ)) ^ ℓ * (ℓ : ℝ) ^ ℓ := by
          rw [← mul_pow, div_mul_cancel₀ _ hℓR]
        have hstep : ((↑(ℓ + 1 : ℕ) : ℝ) / (ℓ : ℝ)) ^ ℓ ≤ 3 := by
          have hconv : (1 + (1 : ℝ) / (ℓ : ℝ)) ^ ℓ ≤ 3 := one_add_inv_pow_le_three ℓ hℓ1
          calc
            ((↑(ℓ + 1 : ℕ) : ℝ) / (ℓ : ℝ)) ^ ℓ = (1 + (1 : ℝ) / (ℓ : ℝ)) ^ ℓ := by
              congr 1
              push_cast
              field_simp [hℓR]
            _ ≤ 3 := hconv
        calc
          (↑(ℓ + 1 : ℕ) : ℝ) ^ (ℓ + 1)
              = (↑(ℓ + 1 : ℕ) : ℝ) ^ ℓ * (↑(ℓ + 1 : ℕ) : ℝ) := by
                rw [pow_succ]
          _ = ((↑(ℓ + 1 : ℕ) : ℝ) / (ℓ : ℝ)) ^ ℓ * (ℓ : ℝ) ^ ℓ * (↑(ℓ + 1 : ℕ) : ℝ) := by
                rw [hdec]
          _ ≤ ((↑(ℓ + 1 : ℕ) : ℝ) / (ℓ : ℝ)) ^ ℓ * (3 ^ ℓ * (ℓ.factorial : ℝ)) * (↑(ℓ + 1 : ℕ) : ℝ) := by
                gcongr
          _ ≤ 3 * (3 ^ ℓ * (ℓ.factorial : ℝ)) * (↑(ℓ + 1 : ℕ) : ℝ) := by
                gcongr
          _ = 3 ^ (ℓ + 1) * ((ℓ + 1).factorial : ℝ) := by
                rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one, pow_succ]
                ac_rfl

/-- Binomial coefficient bound: `n.choose ℓ ≤ (3n/ℓ)^ℓ` for `1 ≤ ℓ ≤ n` (real). -/
theorem choose_le_three_pow_div {n ℓ : ℕ} (hℓ0 : 1 ≤ ℓ) (hℓn : ℓ ≤ n) :
    (n.choose ℓ : ℝ) ≤ (3 * (n : ℝ) / ℓ) ^ ℓ := by
  have hℓpos : 0 < (ℓ : ℝ) := by exact_mod_cast (lt_of_lt_of_le zero_lt_one hℓ0)
  have hfac : 0 < (ℓ.factorial : ℝ) := by exact_mod_cast (Nat.factorial_pos ℓ)
  have hℓpow : 0 < (ℓ : ℝ) ^ ℓ := pow_pos hℓpos ℓ
  have hnpow0 : 0 ≤ (n : ℝ) ^ ℓ := pow_nonneg (by positivity) ℓ
  calc
    (n.choose ℓ : ℝ) ≤ (n : ℝ) ^ ℓ / (ℓ.factorial : ℝ) := by
      simpa using (Nat.choose_le_pow_div (α := ℝ) (r := ℓ) (n := n))
    _ ≤ (3 * (n : ℝ) / ℓ) ^ ℓ := by
      have hRHS : (3 * (n : ℝ) / ℓ) ^ ℓ = (3 ^ ℓ * (n : ℝ) ^ ℓ) / (ℓ : ℝ) ^ ℓ := by
        rw [div_pow, mul_pow]
      rw [hRHS]
      rw [div_le_div_iff₀ hfac hℓpow]
      have h2 := pow_le_three_pow_factorial ℓ
      have hmul : (n : ℝ) ^ ℓ * (ℓ : ℝ) ^ ℓ ≤
          (n : ℝ) ^ ℓ * (3 ^ ℓ * (ℓ.factorial : ℝ)) := by
        exact mul_le_mul_of_nonneg_left h2 hnpow0
      simpa [mul_assoc, mul_comm, mul_left_comm] using hmul

/-- Finite geometric tail: for `0 ≤ ρ ≤ 1/2`, `Σ_{k=1}^n ρ^k ≤ 2ρ`. -/
theorem geom_tail_le_two_mul {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ : ρ ≤ 1 / 2) (n : ℕ) :
    (∑ k ∈ Finset.range n, ρ ^ (k + 1)) ≤ 2 * ρ := by
  induction n with
  | zero =>
      simp
      nlinarith
  | succ n ih =>
      calc
        (∑ k ∈ Finset.range (n + 1), ρ ^ (k + 1))
            = ρ + ρ * (∑ k ∈ Finset.range n, ρ ^ (k + 1)) := by
              rw [Finset.sum_range_succ']
              rw [show (∑ k ∈ Finset.range n, ρ ^ (k + 2)) =
                  ρ * (∑ k ∈ Finset.range n, ρ ^ (k + 1)) by
                    rw [Finset.mul_sum]
                    apply Finset.sum_congr rfl
                    intro k hk
                    have hk' : k + 2 = (k + 1) + 1 := by omega
                    rw [hk', pow_succ]
                    ring]
              simp [pow_one]
              abel
        _ ≤ ρ + ρ * (2 * ρ) := by
              exact add_le_add_right (mul_le_mul_of_nonneg_left ih hρ0) ρ
        _ ≤ 2 * ρ := by
              have hρ2 : 2 * ρ ^ 2 ≤ ρ := by
                have hm := mul_le_mul_of_nonneg_left hρ hρ0
                nlinarith
              nlinarith

/-- finite geometric full sum ≤ 2ρ for 0 ≤ ρ ≤ 1/2, over k from 1 to n. -/
theorem geom_Icc_le_two_mul {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ : ρ ≤ 1 / 2) (n : ℕ) :
    (∑ k ∈ Finset.Icc 1 n, ρ ^ k) ≤ 2 * ρ := by
  have htail : (∑ k ∈ Finset.Icc 1 n, ρ ^ k) = ∑ k ∈ Finset.range n, ρ ^ (k + 1) := by
    induction n with
    | zero =>
        simp
    | succ n ih =>
        calc
          (∑ k ∈ Finset.Icc 1 (n + 1), ρ ^ k)
              = (∑ k ∈ Finset.Icc 1 n, ρ ^ k) + ρ ^ (n + 1) := by
                rw [Finset.sum_Icc_succ_top (by omega) (fun k => ρ ^ k)]
          _ = (∑ k ∈ Finset.range n, ρ ^ (k + 1)) + ρ ^ (n + 1) := by rw [ih]
          _ = ∑ k ∈ Finset.range (n + 1), ρ ^ (k + 1) := by
                rw [Finset.sum_range_succ]
  rw [htail]
  exact geom_tail_le_two_mul hρ0 hρ n

end Est
end Submission
