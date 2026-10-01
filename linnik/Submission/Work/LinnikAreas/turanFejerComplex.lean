import Mathlib
import Submission.Work.LinnikAreas.turanFejerLower

namespace Work.LinnikAreas

open scoped BigOperators

/-- Complex-to-real bridge: for a complex number `w` and a natural `j`,
`Re (w ^ j) = ‖w‖ ^ j * cos (j * arg w)`.

This is the polar decomposition `w = ‖w‖ * exp (arg w * I)`. -/
lemma re_pow_eq_norm_pow_cos_arg (w : ℂ) (j : ℕ) :
    (w ^ j).re = ‖w‖ ^ j * Real.cos ((j : ℝ) * Complex.arg w) := by
  have hE : Complex.exp ((Complex.arg w : ℂ) * Complex.I) ^ j
      = Complex.exp (((j : ℝ) * Complex.arg w : ℝ) * Complex.I) := by
    rw [← Complex.exp_nat_mul]; congr 1; push_cast; ring
  conv_lhs => rw [← Complex.norm_mul_exp_arg_mul_I w]
  rw [mul_pow, ← Complex.ofReal_pow, hE, Complex.re_ofReal_mul, Complex.exp_ofReal_mul_I_re]

theorem turanFejerComplex (J : ℕ) (hJ : 1 ≤ J) (w : ℂ) (hw : ‖w‖ ≤ 1) :
    -‖w‖ / (1 + ‖w‖) ≤
      ∑ j ∈ Finset.Icc 1 J, (1 - (j : ℝ) / (J + 1)) * (w ^ j).re := by
  have h := Work.LinnikAreas.turanFejerLower J hJ (r := ‖w‖) (θ := Complex.arg w)
    (norm_nonneg w) hw
  have hsum : ∑ j ∈ Finset.Icc 1 J,
        (1 - (j : ℝ) / (J + 1)) * ‖w‖ ^ j * Real.cos ((j : ℝ) * Complex.arg w)
      = ∑ j ∈ Finset.Icc 1 J, (1 - (j : ℝ) / (J + 1)) * (w ^ j).re := by
    apply Finset.sum_congr rfl
    intro j _
    rw [re_pow_eq_norm_pow_cos_arg w j]
    ring
  rw [hsum] at h
  rw [← neg_div] at h
  exact h

end Work.LinnikAreas
