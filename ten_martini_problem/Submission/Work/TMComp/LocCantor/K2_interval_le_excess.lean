import Mathlib
import Submission.Work.TMComp.LocCantor.C8_jump
import Submission.Work.TMComp.LocCantor.K2_integral_le
import Submission.Work.TMComp.LocCantor.K2_pointwise_eq

namespace Work.TMComp.LocCantor

open MeasureTheory Work.TMComp.Kotani

/-- The (K2)-integrand agrees pointwise with the integrand of `K2_integral_le` when
`E` is of the form `E₀ + iε` with `ε > 0` (so that `E.im = ε > 0`). -/
theorem K2_eq_integrand (α lam : ℝ) {ε : ℝ} (hε : 0 < ε) (E : ℝ) :
    (fun y : ℝ => K2 α lam ((E : ℂ) + (ε : ℂ) * Complex.I) y)
      = fun y : ℝ => 1 / N1 α lam ((E : ℂ) + (ε : ℂ) * Complex.I) y
          + 1 / N2 α lam ((E : ℂ) + (ε : ℂ) * Complex.I) y
          - 4 * (-1 / defect α lam ((E : ℂ) + (ε : ℂ) * Complex.I) y).im := by
  have hEim : ((E : ℂ) + (ε : ℂ) * Complex.I).im = ε := by simp
  have hE : 0 < ((E : ℂ) + (ε : ℂ) * Complex.I).im := by rw [hEim]; exact hε
  funext y
  rw [K2]
  exact (K2_pointwise_eq α lam y hE).symm

/-- The `y`-integral of the (K2)-integrand over one period is bounded by `4` times the
"excess" `ℓ/ε - ∫ (-1/defect).im`.  Immediate from the pointwise identity
`K2_pointwise_eq` and the integrated bound `K2_integral_le`. -/
theorem K2_interval_le_excess (α lam : ℝ) {ε : ℝ} (hε : 0 < ε) (E : ℝ) :
    ∫ y in (0 : ℝ)..1, Work.TMComp.LocCantor.K2 α lam ((E : ℂ) + (ε : ℂ) * Complex.I) y
      ≤ 4 * (Work.TMComp.Kotani.ell α lam ((E : ℂ) + (ε : ℂ) * Complex.I) / ε
          - ∫ y in (0 : ℝ)..1, (-1 / Work.TMComp.Kotani.defect α lam ((E : ℂ) + (ε : ℂ) * Complex.I) y).im) := by
  rw [K2_eq_integrand α lam hε E]
  exact K2_integral_le α lam E ε hε

end Work.TMComp.LocCantor
