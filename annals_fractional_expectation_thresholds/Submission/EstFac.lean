import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Analysis.Complex.ExponentialBounds

open scoped BigOperators
namespace Submission
namespace EstFac

/-- A factorial lower bound: `(ℓ/3)^ℓ ≤ ℓ!` for ℓ ≥ 1 (equivalent real form: `3^ℓ · ℓ! ≥ ℓ^ℓ`). -/
theorem pow_le_three_pow_factorial (ℓ : ℕ) : (ℓ : ℝ) ^ ℓ ≤ 3 ^ ℓ * (ℓ.factorial : ℝ) := by
  induction ℓ with
  | zero =>
      norm_num
  | succ ℓ ih =>
      by_cases hℓz : ℓ = 0
      · subst ℓ
        norm_num
      · have hℓR : (ℓ : ℝ) ≠ 0 := by exact_mod_cast hℓz
        have hdec : ((↑(ℓ + 1 : ℕ) : ℝ) / (ℓ : ℝ)) ^ ℓ * (ℓ : ℝ) ^ ℓ =
            (↑(ℓ + 1 : ℕ) : ℝ) ^ ℓ := by
          rw [← mul_pow, div_mul_cancel₀ _ hℓR]
        have hstep : ((↑(ℓ + 1 : ℕ) : ℝ) / (ℓ : ℝ)) ^ ℓ ≤ 3 := by
          have h1 : (1 + (ℓ : ℝ)⁻¹) ^ ℓ ≤ Real.exp 1 :=
            Real.one_add_inv_pow_le_exp (n := ℓ)
          have hconv : (1 + (ℓ : ℝ)⁻¹) ^ ℓ = ((↑(ℓ + 1 : ℕ) : ℝ) / (ℓ : ℝ)) ^ ℓ := by
            congr 1
            push_cast
            field_simp [hℓR]
          calc
            ((↑(ℓ + 1 : ℕ) : ℝ) / (ℓ : ℝ)) ^ ℓ = (1 + (ℓ : ℝ)⁻¹) ^ ℓ := by rw [hconv]
            _ ≤ Real.exp 1 := h1
            _ ≤ 3 := (Real.exp_one_lt_three).le
        calc
          (↑(ℓ + 1 : ℕ) : ℝ) ^ (ℓ + 1)
              = (↑(ℓ + 1 : ℕ) : ℝ) ^ ℓ * (↑(ℓ + 1 : ℕ) : ℝ) := by
                rw [pow_succ]
          _ = ((↑(ℓ + 1 : ℕ) : ℝ) / (ℓ : ℝ)) ^ ℓ * (ℓ : ℝ) ^ ℓ * (↑(ℓ + 1 : ℕ) : ℝ) := by
                rw [← hdec]
          _ ≤ ((↑(ℓ + 1 : ℕ) : ℝ) / (ℓ : ℝ)) ^ ℓ * (3 ^ ℓ * (ℓ.factorial : ℝ)) * (↑(ℓ + 1 : ℕ) : ℝ) := by
                gcongr
          _ ≤ 3 * (3 ^ ℓ * (ℓ.factorial : ℝ)) * (↑(ℓ + 1 : ℕ) : ℝ) := by
                gcongr
          _ = 3 ^ (ℓ + 1) * ((ℓ + 1).factorial : ℝ) := by
                rw [Nat.factorial_succ, Nat.cast_mul, pow_succ]
                ac_rfl
end EstFac
end Submission
