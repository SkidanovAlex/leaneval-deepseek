import Mathlib
import Submission.Commons.NumberTheory.Zeta.summable_vonMangoldt_div_rpow

namespace Work.LinnikAreas.OtherCharRepel

/-- For `σ > 1` the series `∑_n Λ(n) · Re(χ n) · n^{-σ}` converges absolutely.

This is a termwise-comparison statement: a Dirichlet character has values of modulus at
most one (`DirichletCharacter.norm_le_one`), so `|Re(χ n)| ≤ 1`, `Λ n ≥ 0` and
`n^{-σ} ≥ 0` give the pointwise bound
`‖Λ n · Re(χ n) · n^{-σ}‖ ≤ Λ n · n^{-σ} = Λ n / n^σ`,
and the majorant converges for `σ > 1` by `Commons.NumberTheory.Zeta.summable_vonMangoldt_div_rpow`. -/
theorem summableVonMangoldtReCharMulRpow {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    {σ : ℝ} (hσ : 1 < σ) :
    Summable (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℝ) * (χ (n : ZMod N)).re *
        (n : ℝ) ^ (-σ)) := by
  -- the real majorant `Λ n · n^{-σ}` is summable for `σ > 1`
  have hsm : Summable (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-σ)) := by
    refine (summable_congr ?_).mpr (Commons.NumberTheory.Zeta.summable_vonMangoldt_div_rpow hσ)
    intro n
    rw [Real.rpow_neg (Nat.cast_nonneg n), div_eq_mul_inv]
  -- termwise comparison
  refine Summable.of_norm_bounded hsm (fun n => ?_)
  have hΛ : 0 ≤ (ArithmeticFunction.vonMangoldt n : ℝ) := ArithmeticFunction.vonMangoldt_nonneg
  have hr : 0 ≤ (n : ℝ) ^ (-σ) := Real.rpow_nonneg (Nat.cast_nonneg n) _
  have ha : |(χ (n : ZMod N)).re| ≤ 1 :=
    le_trans (Complex.abs_re_le_norm _) (χ.norm_le_one _)
  rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg hΛ, abs_of_nonneg hr]
  calc (ArithmeticFunction.vonMangoldt n : ℝ) * |(χ (n : ZMod N)).re| * (n : ℝ) ^ (-σ)
      ≤ (ArithmeticFunction.vonMangoldt n : ℝ) * 1 * (n : ℝ) ^ (-σ) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ha hΛ) hr
    _ = (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-σ) := by ring

end Work.LinnikAreas.OtherCharRepel
