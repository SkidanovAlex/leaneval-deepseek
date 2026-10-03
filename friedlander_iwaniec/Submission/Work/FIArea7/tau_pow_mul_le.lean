import Mathlib
import Submission.Work.FIArea7.psiTauMul

namespace Work.FIArea7

/-- `τ(m n) ≤ τ(m) τ(n)` (submultiplicativity of the divisor-count function), raised to the power
`j`.  Immediate from `psiTauMul` and monotonicity of `x ↦ x ^ j` on `ℝ≥0`. -/
theorem tau_pow_mul_le (j m n : ℕ) :
    ((((m * n).divisors.card : ℕ) : ℝ)) ^ j
      ≤ ((((m.divisors.card : ℕ) : ℝ)) ^ j) * ((((n.divisors.card : ℕ) : ℝ)) ^ j) := by
  have h : (((m * n).divisors.card : ℕ) : ℝ)
      ≤ ((m.divisors.card : ℕ) : ℝ) * ((n.divisors.card : ℕ) : ℝ) := by
    exact_mod_cast psiTauMul m n
  calc ((((m * n).divisors.card : ℕ) : ℝ)) ^ j
      ≤ ((((m.divisors.card : ℕ) : ℝ) * ((n.divisors.card : ℕ) : ℝ))) ^ j :=
        pow_le_pow_left₀ (by positivity) h j
    _ = ((((m.divisors.card : ℕ) : ℝ)) ^ j) * ((((n.divisors.card : ℕ) : ℝ)) ^ j) :=
        mul_pow _ _ _

end Work.FIArea7
