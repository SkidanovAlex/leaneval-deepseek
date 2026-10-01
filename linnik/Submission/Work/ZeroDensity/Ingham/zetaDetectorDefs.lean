import Mathlib
import Submission.Work.ZeroDensity.Ingham.Defs

/-!
# Vocabulary for Montgomery's zero detector for `ζ` (`Work.ZeroDensity.Ingham.zetaDetector`)

The objects of the detector: the Perron integrand `perronInt`, its residue `residueTerm`
at the pole `w = 1 - ρ`, the truncated detector sum `detTail`, the discarded far tail
`detFarTail`, the full smoothed Dirichlet sum `detSum`, and the critical–line integrand
`critIntegrand` with its truncated integral `critIntegral`.
-/

namespace Work.ZeroDensity.Ingham

open scoped Classical BigOperators
open MeasureTheory

/-- The Mellin (Perron) integrand `Γ(w) Y^w ζ(ρ+w) M_K(ρ+w)`. -/
noncomputable def perronInt (K : ℕ) (Y : ℝ) (ρ w : ℂ) : ℂ :=
  Complex.Gamma w * (Y : ℂ) ^ w * riemannZeta (ρ + w) * MK K (ρ + w)

/-- The residue of `perronInt` at the pole `w = 1 - ρ`: `Γ(1-ρ) Y^{1-ρ} M_K(1)`. -/
noncomputable def residueTerm (K : ℕ) (Y : ℝ) (ρ : ℂ) : ℂ :=
  Complex.Gamma (1 - ρ) * (Y : ℂ) ^ (1 - ρ) * MK K 1

/-- The full exponentially smoothed Dirichlet sum `Σ_n a_K(n) n^{-ρ} e^{-n/Y}`. -/
noncomputable def detSum (K : ℕ) (Y : ℝ) (ρ : ℂ) : ℂ :=
  ∑' n : ℕ, mCoef K n * (n : ℂ) ^ (-ρ) * Complex.exp (-(n : ℂ) / Y)

/-- The truncated detector tail `Σ_{K<n≤Z} a_K(n) n^{-ρ} e^{-n/Y}`. -/
noncomputable def detTail (K : ℕ) (Y Z : ℝ) (ρ : ℂ) : ℂ :=
  ∑ n ∈ Finset.Ioc K ⌊Z⌋₊, mCoef K n * (n : ℂ) ^ (-ρ) * Complex.exp (-(n : ℂ) / Y)

/-- The discarded far tail `Σ_{n>Z} a_K(n) n^{-ρ} e^{-n/Y}`. -/
noncomputable def detFarTail (K : ℕ) (Y Z : ℝ) (ρ : ℂ) : ℂ :=
  ∑' n : ℕ, if ⌊Z⌋₊ < n then mCoef K n * (n : ℂ) ^ (-ρ) * Complex.exp (-(n : ℂ) / Y) else 0

/-- The critical–line integrand `‖ζ(1/2+i Im ρ+iv)‖ ‖M_K(1/2+i Im ρ+iv)‖ ‖Γ(1/2-Re ρ+iv)‖`. -/
noncomputable def critIntegrand (K : ℕ) (ρ : ℂ) (v : ℝ) : ℝ :=
  ‖riemannZeta ((1 / 2 : ℂ) + (ρ.im : ℂ) * Complex.I + (v : ℂ) * Complex.I)‖ *
    ‖MK K ((1 / 2 : ℂ) + (ρ.im : ℂ) * Complex.I + (v : ℂ) * Complex.I)‖ *
      ‖Complex.Gamma (((1 / 2 : ℝ) - ρ.re : ℝ) + (v : ℝ) * Complex.I)‖

/-- The truncated critical–line integral `∫_{-L}^{L} critIntegrand K ρ v dv`. -/
noncomputable def critIntegral (K : ℕ) (ρ : ℂ) (L : ℝ) : ℝ :=
  ∫ v in (-L)..L, critIntegrand K ρ v

end Work.ZeroDensity.Ingham
