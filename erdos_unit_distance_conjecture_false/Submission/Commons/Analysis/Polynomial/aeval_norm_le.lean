import Mathlib.Analysis.Polynomial.Norm

/-!
# Sup-norm bound for polynomial evaluation in an extension

Evaluating (in `L`) a polynomial `p : K[X]` at an element `x : L` of a normed
extension field `L` of `K` (whose norm extends the norm on `K`, in the sense of
`h_ext`) costs at most the number of coefficients times the sup-norm of the
coefficients times a power of `max 1 ‖x‖`:

`‖(aeval x) p‖ ≤ (natDegree + 1) * supNorm p * (max 1 ‖x‖) ^ natDegree`.
-/

open scoped Polynomial BigOperators

namespace Commons.Analysis.Polynomial

/-- In a normed field extension whose norm extends the norm on the base field,
scalar multiplication is norm-multiplicative: `‖a • y‖ = ‖a‖ * ‖y‖`. -/
lemma norm_smul_eq {K L : Type*} [NormedField K] [NormedField L] [Algebra K L]
    (h_ext : ∀ k : K, ‖algebraMap K L k‖ = ‖k‖) (a : K) (y : L) :
    ‖a • y‖ = ‖a‖ * ‖y‖ := by
  rw [Algebra.smul_def, norm_mul, h_ext]

/-- Evaluating a polynomial with coefficients in `K` at an element `x : L` of
a normed extension field: bounded by the number of coefficients times the
sup-norm of the coefficients times a power of `max 1 ‖x‖`. -/
lemma aeval_norm_le {K L : Type*} [NormedField K] [NormedField L] [Algebra K L]
    (h_ext : ∀ k : K, ‖algebraMap K L k‖ = ‖k‖) (p : Polynomial K) (x : L) :
    ‖(Polynomial.aeval x) p‖ ≤ (p.natDegree + 1 : ℝ) * p.supNorm * (max 1 ‖x‖) ^ p.natDegree := by
  let M : ℝ := max 1 ‖x‖
  have hM1 : 1 ≤ M := le_max_left _ _
  have hMx : ‖x‖ ≤ M := le_max_right _ _
  calc
    ‖(Polynomial.aeval x) p‖ = ‖∑ i ∈ Finset.range (p.natDegree + 1), p.coeff i • x ^ i‖ := by
      rw [Polynomial.aeval_eq_sum_range]
    _ ≤ ∑ i ∈ Finset.range (p.natDegree + 1), ‖p.coeff i • x ^ i‖ := norm_sum_le _ _
    _ ≤ ∑ i ∈ Finset.range (p.natDegree + 1), p.supNorm * M ^ p.natDegree := by
      refine Finset.sum_le_sum ?_
      intro i hi
      have hile : i ≤ p.natDegree := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
      calc
        ‖p.coeff i • x ^ i‖ = ‖p.coeff i‖ * ‖x‖ ^ i := by
          rw [norm_smul_eq h_ext, norm_pow]
        _ ≤ p.supNorm * ‖x‖ ^ i := by
          exact mul_le_mul_of_nonneg_right (p.le_supNorm i) (pow_nonneg (norm_nonneg x) i)
        _ ≤ p.supNorm * M ^ i := by
          exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg x) hMx i) p.supNorm_nonneg
        _ ≤ p.supNorm * M ^ p.natDegree := by
          exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hM1 hile) p.supNorm_nonneg
    _ = (p.natDegree + 1 : ℝ) * (p.supNorm * M ^ p.natDegree) := by
      simp [Finset.sum_const]
    _ = (p.natDegree + 1 : ℝ) * p.supNorm * M ^ p.natDegree := by ring
    _ = (p.natDegree + 1 : ℝ) * p.supNorm * (max 1 ‖x‖) ^ p.natDegree := by simp [M]

end Commons.Analysis.Polynomial
