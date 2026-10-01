import Mathlib

namespace Work.LinnikAreas.Density4.Udecay

/-- For `s > 0` the Dirichlet series of the Möbius function at the real point `1 + s`
(which lies in the half-plane of absolute convergence `Re > 1`) sums to the real part of
the reciprocal of the Riemann zeta function, i.e. `∑_{n} μ(n)/n^{1+s} = 1/ζ(1+s)`. -/
theorem mu_series_zeta_inv (s : ℝ) (hs : 0 < s) :
    (∑' n : ℕ, (ArithmeticFunction.moebius n : ℝ) / (n : ℝ) ^ (1 + s : ℝ))
      = ((riemannZeta ((1 + s : ℝ) : ℂ))⁻¹).re := by
  set S : ℂ := ((1 + s : ℝ) : ℂ) with hSdef
  have hS1 : 1 < S.re := by rw [hSdef]; simp; linarith
  have hSne : S ≠ 0 := by
    intro h; rw [h] at hS1; norm_num at hS1
  -- The complex L-series of the Möbius function is the reciprocal of ζ at `S`.
  have hmu : LSeries (fun n => (ArithmeticFunction.moebius n : ℂ)) S = (riemannZeta S)⁻¹ := by
    have h := LSeries_one_mul_Lseries_moebius hS1
    rw [LSeries_one_eq_riemannZeta hS1] at h
    exact (inv_eq_of_mul_eq_one_right h).symm
  -- Spell the L-series out as an explicit `tsum`.
  have hLSsum : LSeries (fun n => (ArithmeticFunction.moebius n : ℂ)) S
      = ∑' n : ℕ, (ArithmeticFunction.moebius n : ℂ) / (n : ℂ) ^ S := by
    rw [LSeries]
    exact tsum_congr (fun n => LSeries.term_of_ne_zero' hSne _ n)
  -- Its real part is the real Dirichlet series in the statement.
  have hcplx : (∑' n : ℕ, (ArithmeticFunction.moebius n : ℂ) / (n : ℂ) ^ S).re
      = ∑' n : ℕ, (ArithmeticFunction.moebius n : ℝ) / (n : ℝ) ^ (1 + s : ℝ) := by
    have h2 : (∑' n : ℕ, (ArithmeticFunction.moebius n : ℂ) / (n : ℂ) ^ S)
        = ((∑' n : ℕ, (ArithmeticFunction.moebius n : ℝ) / (n : ℝ) ^ (1 + s : ℝ) : ℝ) : ℂ) := by
      rw [Complex.ofReal_tsum]
      refine tsum_congr (fun n => ?_)
      rw [Complex.ofReal_div, Complex.ofReal_cpow (Nat.cast_nonneg n) (1 + s)]
      simp [hSdef]
    rw [h2, Complex.ofReal_re]
  rw [← hcplx, ← hLSsum, hmu, hSdef]

end Work.LinnikAreas.Density4.Udecay
