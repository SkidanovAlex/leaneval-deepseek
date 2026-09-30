import Mathlib
import Submission.Work.BMF.norm_cpow_I_eq_one

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF.pcsw

/-- **Pointwise bound for one summand of the `1/log`-weighted twisted von Mangoldt sum.**
For `n ≥ 2`, `‖(log n)⁻¹ · Λ(n) · χ(n) · n^{it}‖ ≤ 1`.

Route: `‖·‖` is multiplicative over the product; `‖(log n)⁻¹‖ = (log n)⁻¹` because `log n > 0`;
`‖Λ n‖ = Λ n` (`ArithmeticFunction.vonMangoldt_nonneg`); `‖χ n‖ ≤ 1`
(`DirichletCharacter.norm_le_one`); `‖n^{it}‖ = 1` (`Work.BMF.norm_cpow_I_eq_one`). Then
`Λ n / log n ≤ 1` since `Λ n ≤ log n` (`ArithmeticFunction.vonMangoldt_le_log`). -/
lemma norm_inv_log_mul_vonMangoldt_mul_chi_mul_cpow_le_one
    (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (t : ℝ) {n : ℕ} (hn : 2 ≤ n) :
    ‖((Real.log n : ℝ) : ℂ)⁻¹ *
        (((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) * χ n * (n : ℂ) ^ (Complex.I * t))‖ ≤ 1 := by
  have hn1 : (1:ℝ) < (n:ℝ) := by
    have h : (1:ℕ) < n := by omega
    exact_mod_cast h
  have hnpos : (0:ℝ) < (n:ℝ) := by linarith
  have hlogpos : (0:ℝ) < Real.log n := Real.log_pos hn1
  have hlog_nonneg : (0:ℝ) ≤ Real.log n := le_of_lt hlogpos
  have hvm_nonneg : (0:ℝ) ≤ ArithmeticFunction.vonMangoldt n :=
    ArithmeticFunction.vonMangoldt_nonneg
  have hchi : ‖χ n‖ ≤ 1 := DirichletCharacter.norm_le_one χ _
  have hcpow : ‖(n : ℂ) ^ (Complex.I * t)‖ = 1 := by
    simpa using Work.BMF.norm_cpow_I_eq_one t (n:ℝ) hnpos
  have hloginv : ‖(((Real.log n : ℝ) : ℂ))⁻¹‖ = (Real.log n)⁻¹ := by
    rw [norm_inv, Complex.norm_real, Real.norm_of_nonneg hlog_nonneg]
  have hvmn : ‖(((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ))‖ =
      ArithmeticFunction.vonMangoldt n := by
    rw [Complex.norm_real, Real.norm_of_nonneg hvm_nonneg]
  have hvmle : ArithmeticFunction.vonMangoldt n ≤ Real.log n :=
    ArithmeticFunction.vonMangoldt_le_log
  calc ‖((Real.log n : ℝ) : ℂ)⁻¹ *
        (((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) * χ n * (n : ℂ) ^ (Complex.I * t))‖
      = (Real.log n)⁻¹ * (ArithmeticFunction.vonMangoldt n * ‖χ n‖) := by
          rw [norm_mul, norm_mul, norm_mul, hloginv, hvmn, hcpow, mul_one]
    _ ≤ (Real.log n)⁻¹ * Real.log n := by
          apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr hlog_nonneg)
          nlinarith [hchi, norm_nonneg (χ n), hvmle, hlog_nonneg, hvm_nonneg]
    _ = 1 := by field_simp

end Work.BMF.pcsw
