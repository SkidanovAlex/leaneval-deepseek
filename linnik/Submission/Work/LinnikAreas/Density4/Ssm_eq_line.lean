/-
# Area 4 / HB §11 (11.9) — the inverse-Mellin representation of `Ssm`

Namespace `Work.LinnikAreas.Density4`.

HB (1992) §11 writes the smoothed sum `Ssm = Σ_n Ψ(n)Θ(n)χ(n)·n^{-ρ}·e^{-n/X}`; this file
identifies it with the contour integral

`Ssm = (1/(2π)) ∫_ℝ Γ(1+it)·X^{1+it}·Σ_n Ψ(n)Θ(n)χ(n)·n^{-(ρ+1+it)} dt`,

i.e. `Ssm = (1/(2π)) ∫_ℝ Γ(1+it) X^{1+it} mollSeries(ρ + (1+it)) dt`.

The proof is the termwise inverse Mellin transform of the exponential kernel
(`mellin_kernel_exp`: `(1/(2π)) ∫_ℝ y^{-(1+it)}Γ(1+it) dt = e^{-y}` for `y > 0`), applied with
`y = n/X`, followed by an exchange of sum and integral which is justified by the absolute
convergence `Σ_n ‖Ψ(n)Θ(n)χ(n)‖ n^{-(Re ρ + 1)} < ∞` (hypothesis `hsum`) together with the
exponential decay of `Γ` on the vertical line `Re s = 1`.

The integrand is packaged as `SsmTerm` (see `SsmTermDefs`); the three ingredients are the
delegated lemmas `SsmTerm_integral` (termwise Mellin inversion), `SsmTerm_tsum_eq` (the
pointwise identification of `Σ_n SsmTerm n t` with `Γ(1+it)X^{1+it}mollSeries(ρ+1+it)`) and
`SsmTerm_tsum_integral` (the sum/integral exchange).
-/
import Mathlib
import Submission.Work.LinnikAreas.Density4.SsmSetup
import Submission.Work.LinnikAreas.Density4.SsmTermDefs
import Submission.Work.LinnikAreas.Density4.SsmTerm_integral
import Submission.Work.LinnikAreas.Density4.SsmTerm_tsum_eq
import Submission.Work.LinnikAreas.Density4.SsmTerm_tsum_integral
import Submission.Work.LinnikAreas.Density4.mellin_kernel_exp

open DirichletCharacter Complex MeasureTheory
open scoped Classical BigOperators
noncomputable section

namespace Work.LinnikAreas.Density4

theorem Ssm_eq_line (q : ℕ) [NeZero q] (U V W X : ℝ) (χ : DirichletCharacter ℂ q) (ρ : ℂ)
    (hX : 0 < X) (hβ : 0 < ρ.re)
    (hsum : Summable (fun n : ℕ => ‖mollCoeff q U V W χ n‖ * (n : ℝ) ^ (-(ρ.re + 1)))) :
    Ssm q U V W X χ ρ
      = (1 / (2 * Real.pi)) * ∫ t : ℝ, Complex.Gamma ((1 : ℂ) + (t : ℂ) * Complex.I)
          * (X : ℂ) ^ ((1 : ℂ) + (t : ℂ) * Complex.I)
          * mollSeries q U V W χ (ρ + ((1 : ℂ) + (t : ℂ) * Complex.I)) := by
  -- `Ssm` is the termwise exponential smoothing of `Σ_n Ψ(n)Θ(n)χ(n)n^{-ρ}`.
  rw [Ssm_eq_tsum_mollCoeff]
  -- Replace each summand by `(1/(2π)) ∫_ℝ SsmTerm n` (termwise inverse Mellin transform).
  rw [show (∑' n : ℕ, mollCoeff q U V W χ n * ((n : ℂ) ^ (-ρ))
        * ((Real.exp (-(n:ℝ)/X) : ℝ) : ℂ))
      = ∑' n : ℕ, (1 / (2 * Real.pi)) * ∫ t : ℝ, SsmTerm q U V W X χ ρ n t from
    tsum_congr fun n => (SsmTerm_integral q U V W X χ ρ hX n).symm]
  -- Pull the constant `1/(2π)` out of the series.
  rw [tsum_mul_left]
  -- Exchange sum and integral.
  rw [SsmTerm_tsum_integral q U V W X χ ρ hX hβ hsum]
  congr 1
  -- Identify the pointwise sum with `Γ(1+it)X^{1+it}mollSeries(ρ + (1+it))`.
  exact integral_congr_ae
    (Filter.Eventually.of_forall fun t => SsmTerm_tsum_eq q U V W X χ ρ hX t)

end Work.LinnikAreas.Density4
