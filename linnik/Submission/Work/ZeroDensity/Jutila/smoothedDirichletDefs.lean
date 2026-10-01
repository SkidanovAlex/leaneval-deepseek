/-
# Jutila (2.11): the integrand of the inverse-Mellin (Mellin) representation

Namespace `Work.ZeroDensity.Jutila`.

For an arbitrary coefficient sequence `b : ℕ → ℂ`, a scale `X > 0`, an exponent `s : ℂ` and
a vertical line `Re w = c` (`c > 0`), the smoothed Dirichlet sum
`Σ_n b n · n^{-s} · e^{-n/X}` is the inverse Mellin transform of the Dirichlet series
`Σ_n b n · n^{-(s+w)}` against the kernel `Γ(w) X^w`:

`Σ_n b n · n^{-s} e^{-n/X} = (1/2π) ∫_ℝ Γ(c+it) X^{c+it} Σ_n b n·n^{-(s+c+it)} dt`.

Writing `w = c + (t:ℂ)*I`, the `n`-th summand of the integral on the right is

`b n · n^{-s} · ((n/X)^{-w} · Γ(w))`,

whose `(1/2π) ∫_ℝ dt` is the `n`-th term `b n · n^{-s} e^{-n/X}` of the smoothed sum (this is the
inverse Mellin transform of `Γ` at the parameter `c` and `y = n/X`, `mellin_kernel_exp`).

This file only introduces that summand and its elementary interface; the analytic content is
delegated (`smTermIntegral`, `smTerm_tsum_eq`, `smTerm_tsum_integral`) and assembled in
`Submission.Work.ZeroDensity.Jutila.mellinSmoothedDirichlet`.
-/
import Mathlib

namespace Work.ZeroDensity.Jutila

open Complex MeasureTheory

noncomputable section

/-- The `n`-th summand of the inverse-Mellin representation of the exponentially smoothed
Dirichlet sum, at the vertical-line parameter `t` (`w = c + t·I`):
`b n · n^{-s} · (n/X)^{-w} · Γ(w)`.  Its `(1/2π)·∫_ℝ dt` is the `n`-th term `b n·n^{-s}·e^{-n/X}`
of the smoothed sum, and summing in `n` first produces `Γ(w)·X^w·Σ_n b n·n^{-(s+w)}`. -/
def SmTerm (b : ℕ → ℂ) (X : ℝ) (s : ℂ) (c : ℝ) (n : ℕ) (t : ℝ) : ℂ :=
  b n * (n : ℂ) ^ (-s)
    * ((((n : ℝ) / X : ℝ) : ℂ) ^ (-(c + (t : ℂ) * Complex.I))
        * Complex.Gamma (c + (t : ℂ) * Complex.I))

end

end Work.ZeroDensity.Jutila
