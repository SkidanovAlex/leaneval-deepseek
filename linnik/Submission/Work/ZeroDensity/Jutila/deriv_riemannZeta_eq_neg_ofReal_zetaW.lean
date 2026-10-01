import Mathlib
import Submission.Work.ZeroDensity.Jutila.JutilaDefs

namespace Work.ZeroDensity.Jutila

/-- On the real axis, the derivative of the Riemann zeta function is the negative of the
Dirichlet series `zetaW σ = ∑_n (log n) n^{-σ}`, i.e. `ζ'(σ) = -∑_n (log n) n^{-σ}` for `σ > 1`.

This is the real-axis specialisation of `deriv (LSeries 1) s = -LSeries (logMul 1) s`. -/
theorem deriv_riemannZeta_eq_neg_ofReal_zetaW (σ : ℝ) (hσ : 1 < σ) :
    deriv riemannZeta (σ : ℂ) = -(Work.ZeroDensity.Jutila.zetaW σ : ℂ) := by
  have hσ' : (1 : ℝ) < (σ : ℂ).re := by simpa using hσ
  -- `riemannZeta` and the L-series of the constant sequence `1` agree near `σ`.
  have hderiv : deriv riemannZeta (σ : ℂ) = deriv (LSeries (1 : ℕ → ℂ)) (σ : ℂ) :=
    Filter.EventuallyEq.deriv_eq <| Filter.eventuallyEq_iff_exists_mem.mpr
      ⟨{z : ℂ | 1 < z.re}, (isOpen_lt continuous_const Complex.continuous_re).mem_nhds hσ',
        fun z hz => (LSeries_one_eq_riemannZeta hz).symm⟩
  have habs : LSeries.abscissaOfAbsConv (1 : ℕ → ℂ) < (σ : ℂ).re := by
    rw [LSeries.abscissaOfAbsConv_one, Complex.ofReal_re]
    exact EReal.coe_lt_coe_iff.mpr hσ
  rw [hderiv, LSeries_deriv (f := (1 : ℕ → ℂ)) habs]
  congr 1
  -- The complex L-series `∑_n (log n) / n^{σ}` cast to `ℂ` is `∑_n (log n) n^{-σ}`.
  have hterm : ∀ n : ℕ, LSeries.term (LSeries.logMul (1 : ℕ → ℂ)) (σ : ℂ) n
      = ((Real.log n * (n : ℝ) ^ (-σ) : ℝ) : ℂ) := by
    intro n
    rcases eq_or_ne n 0 with rfl | hn
    · simp [LSeries.term, Real.log_zero]
    · rw [LSeries.term_of_ne_zero hn, LSeries.logMul, Pi.one_apply, mul_one]
      change Complex.log ((n : ℝ) : ℂ) / ((n : ℝ) : ℂ) ^ ((σ : ℝ) : ℂ) = _
      rw [← Complex.ofReal_log (Nat.cast_nonneg n), ← Complex.ofReal_cpow (Nat.cast_nonneg n) σ,
        ← Complex.ofReal_div, div_eq_mul_inv, ← Real.rpow_neg (Nat.cast_nonneg n) σ]
  rw [show LSeries (LSeries.logMul (1 : ℕ → ℂ)) (σ : ℂ)
        = ∑' n : ℕ, ((Real.log n * (n : ℝ) ^ (-σ) : ℝ) : ℂ) from tsum_congr hterm,
      ← Complex.ofReal_tsum]
  rfl

end Work.ZeroDensity.Jutila
