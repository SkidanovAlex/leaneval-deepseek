import Mathlib
import Submission.Commons.Analysis.SpecialFunctions.Gamma.gamma_vertical_exp_decay

/-!
# Re-export of the rotated Euler Γ-integral identity

`Submission.Commons.Analysis.SpecialFunctions.Gamma.gamma_vertical_exp_decay` proves the
contour-rotation form of Euler's Γ integral (with no `sorry`).  This thin module re-exports it
under the `Work.ZeroDensity.Zeta` namespace together with the unfolding lemma for `Jr`, so that
the lemmas in this directory can depend on it by an in-workspace path.
-/

namespace Work.ZeroDensity.Zeta

open MeasureTheory Set

/-- The rotated Γ integrand `e^{-r·e^{-iθ}}·r^{s-1}` (`r > 0`). -/
noncomputable def Jrot (s : ℂ) (θ : ℝ) (r : ℝ) : ℂ :=
  Commons.Analysis.SpecialFunctions.Gamma.GRBase.Jr s θ r

theorem Jrot_apply (s : ℂ) (θ r : ℝ) :
    Jrot s θ r
      = Complex.exp (-((r : ℂ) * Complex.exp (-(Complex.I * (θ : ℂ))))) * (r : ℂ) ^ (s - 1) :=
  rfl

/-- **Contour rotation for Euler's Γ integral**:
`Γ(s) = e^{-iθs}·∫_0^∞ e^{-r e^{-iθ}} r^{s-1} dr` for `0 < Re s` and `|θ| < π/2`. -/
theorem gamma_eq_Jrot_integral (s : ℂ) (hs : 0 < s.re) {θ : ℝ} (hθ : |θ| < Real.pi / 2) :
    Complex.Gamma s =
      Complex.exp (-(Complex.I * (θ : ℂ) * s)) *
        ∫ r in Set.Ioi (0 : ℝ), Jrot s θ r :=
  Commons.Analysis.SpecialFunctions.Gamma.GRRect.gamma_eq_Jr_integral s hs hθ

end Work.ZeroDensity.Zeta
