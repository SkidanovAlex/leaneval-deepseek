import Mathlib
import Submission.Work.ZeroDensity.Jutila.JutilaDefs

namespace Work.ZeroDensity.Jutila

/-- For real `σ > 1` the Riemann zeta function agrees with the real Dirichlet series
`zetaZ σ = ∑_{n ≥ 1} n^{-σ}`, i.e. `ζ(σ) = zetaZ σ`. -/
theorem riemannZeta_eq_ofReal_zetaZ (σ : ℝ) (hσ : 1 < σ) :
    riemannZeta (σ : ℂ) = (Work.ZeroDensity.Jutila.zetaZ σ : ℂ) := by
  rw [zeta_eq_tsum_one_div_nat_cpow (by simpa using hσ)]
  rw [zetaZ, Complex.ofReal_tsum]
  refine tsum_congr ?_
  intro n
  have hcast : (n : ℂ) = ((n : ℝ) : ℂ) := by norm_num
  rw [hcast, one_div, ← Complex.ofReal_cpow (Nat.cast_nonneg n) σ, ← Complex.ofReal_inv,
    ← Real.rpow_neg (Nat.cast_nonneg n) σ]

end Work.ZeroDensity.Jutila
