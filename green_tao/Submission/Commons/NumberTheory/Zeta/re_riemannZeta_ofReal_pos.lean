import Mathlib.NumberTheory.LSeries.Dirichlet

open scoped ComplexOrder

namespace Commons.NumberTheory.Zeta

/-- For real `σ > 1`, the Riemann zeta function is real and positive at `σ`.

This is the analytic half-plane version of the classical fact
`ζ(σ) = ∑_{n≥1} n^{-σ} > 0`; here we use `LSeries.positive` applied to the
Dirichlet series of the arithmetic function `ζ`. -/
theorem re_riemannZeta_ofReal_pos {σ : ℝ} (hσ : 1 < σ) :
    0 < (riemannZeta ((σ : ℝ) : ℂ)).re := by
  have hσC : (1 : ℝ) < ((σ : ℂ)).re := by simpa using hσ
  have hmem : LSeries.abscissaOfAbsConv
      (fun n : ℕ => (↑(ArithmeticFunction.zeta n) : ℂ)) < σ := by
    rw [ArithmeticFunction.abscissaOfAbsConv_zeta]
    exact_mod_cast hσ
  have hpos : 0 < LSeries (fun n : ℕ => (↑(ArithmeticFunction.zeta n) : ℂ)) (σ : ℂ) :=
    LSeries.positive (fun n => by rw [ArithmeticFunction.zeta_apply]; split_ifs <;> simp)
      (by rw [ArithmeticFunction.zeta_apply]; norm_num) hmem
  rw [ArithmeticFunction.LSeries_zeta_eq_riemannZeta hσC] at hpos
  exact (Complex.pos_iff.mp hpos).1

end Commons.NumberTheory.Zeta