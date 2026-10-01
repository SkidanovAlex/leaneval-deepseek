import Mathlib

namespace Work.LinnikAreas

/-- The norm of `Λ n · χ(n) / n · w` is at most `Λ n / n · w`, since the values of a
Dirichlet character have norm at most one, `Λ n ≥ 0`, `n > 0` and `w ≥ 0`. -/
theorem NormVonMangoldtMulCharDiv {N : ℕ} [NeZero N] (ψ : DirichletCharacter ℂ N) {n : ℕ} (hn : 1 ≤ n)
    {w : ℝ} (hw : 0 ≤ w) :
    ‖(ArithmeticFunction.vonMangoldt n : ℂ) * (ψ (n : ZMod N) : ℂ) / (n : ℂ) * ((w : ℝ) : ℂ)‖
      ≤ ArithmeticFunction.vonMangoldt n / (n : ℝ) * w := by
  have ha : 0 ≤ ArithmeticFunction.vonMangoldt n := ArithmeticFunction.vonMangoldt_nonneg
  have hb : ‖(ψ (n : ZMod N) : ℂ)‖ ≤ 1 := DirichletCharacter.norm_le_one ψ _
  have hc : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hnorm :
      ‖(ArithmeticFunction.vonMangoldt n : ℂ) * (ψ (n : ZMod N) : ℂ) / (n : ℂ) * ((w : ℝ) : ℂ)‖
        = ArithmeticFunction.vonMangoldt n * ‖(ψ (n : ZMod N) : ℂ)‖ / (n : ℝ) * w := by
    simp only [norm_mul, norm_div, Complex.norm_natCast, Complex.norm_real,
      Real.norm_of_nonneg ha, Real.norm_of_nonneg hw]
  rw [hnorm]
  have h1 : ArithmeticFunction.vonMangoldt n * ‖(ψ (n : ZMod N) : ℂ)‖
      ≤ ArithmeticFunction.vonMangoldt n := by
    simpa using mul_le_mul_of_nonneg_left hb ha
  have h2 : ArithmeticFunction.vonMangoldt n * ‖(ψ (n : ZMod N) : ℂ)‖ / (n : ℝ)
      ≤ ArithmeticFunction.vonMangoldt n / (n : ℝ) :=
    div_le_div_of_nonneg_right h1 (le_of_lt hc)
  exact mul_le_mul_of_nonneg_right h2 hw

end Work.LinnikAreas
