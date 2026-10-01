import Mathlib
import Submission.Work.ZeroDensity.Ingham.zetaPerronDefs

namespace Work.ZeroDensity.Ingham

/-- The Perron integrand `perronInt K Y ρ w = Γ(w)Y^wζ(ρ+w)M_K(ρ+w)` is integrable on the vertical
line `Re w = c` whenever the shifted strip values `Re(ρ+w) = Re ρ + c` lie in `[-1,3]` and the line
avoids the pole `w = 1 - ρ`.  The integrand is exponentially small at `±i∞`: `Γ(w)` decays like
`exp(-(π/2)|Im w|)` (use `norm_Gamma_le_shift_nat` when `c ≤ 0` and `Gamma_vertical_norm_bounds`
elsewhere), `ζ` grows only polynomially (`Commons.NumberTheory.Zeta.zeta_strip_polyGrowth`), and
`M_K` and `Y^w` are bounded on the line.

Suggested route: on the line the integrand agrees with
`perronM K Y ρ (c+it)/((c+it)-(1-ρ))` (`perronInt_eq_perronM_div` in the same module as the
definitions) for every `t ≠ 0`; that function of `t` is continuous and bounded by
`C·exp(-(π/2)|t|)·(1+|t|)^A`, so it is integrable, and `Integrable.congr` transfers. -/
theorem perronInt_integrable (K : ℕ) (Y : ℝ) (hY : 0 < Y) (ρ : ℂ)
    (hζ : riemannZeta ρ = 0) (hρ1 : ρ ≠ 1) {c : ℝ}
    (hc1 : -1 ≤ ρ.re + c) (hc2 : ρ.re + c ≤ 3) (hc3 : c ≠ (1 - ρ).re)
    (hc4 : -1 < c) (hc5 : c ≤ 3) :
    MeasureTheory.Integrable (fun t : ℝ => Work.ZeroDensity.Ingham.perronInt K Y ρ
      ((c : ℂ) + (t : ℂ) * Complex.I)) := by
  sorry

end Work.ZeroDensity.Ingham
