import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.StrongEps.E5Aux2.MuHGlue
import Submission.Work.FTS_RegExport.RXT.continuousAt_integral_Itheta_of_bound
import Submission.Work.FTS_RegExport.RXT.Sys.continuousAt_Qang_of_bounds

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.E5Aux2.L12FtauAux

set_option linter.unusedVariables false

open scoped Real
open MeasureTheory

/-- The `L₁₂`-density is the angular moment `∫ θ in Iθ, K θ * Y s θ` divided by `s`.

This is the definitional unfolding of `Work.FM.L12dens` together with the fact that the
division by the *constant* `s` may be pulled out of the integral. -/
theorem L12dens_eq_thetaIntegral_div (Y : ℝ → ℝ → ℝ) (s : ℝ) :
    Work.FM.L12dens Work.Spaces.K Y s
      = (∫ θ in Work.Spaces.Iθ, Work.Spaces.K θ * Y s θ) / s := by
  rw [Work.FM.L12dens, MeasureTheory.integral_div, Work.Spaces.Iθ]

theorem L12dens_continuousAt_of_bound {Y : ℝ → ℝ → ℝ} {M z : ℝ}
    (hM : 0 ≤ M)
    (hY : ContinuousOn (Function.uncurry Y) Work.FTS.EllipticEst.Q0)
    (hbd : ∀ σ ∈ Set.Ioi (0 : ℝ), ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), |Y σ θ| ≤ M)
    (hz : 0 < z) :
    ContinuousAt (Work.FM.L12dens Work.Spaces.K Y) z := by
  -- The angular moment `s ↦ ∫ θ in Iθ, K θ * Y s θ` is continuous at `z`.
  have hQang : ContinuousAt
      (fun s => ∫ θ in Work.Spaces.Iθ, Work.Spaces.K θ * Y s θ) z := by
    have h := Work.FTS_RegExport.RXT.Sys.continuousAt_Qang_of_bounds (f := Y)
      (s₀ := z) (A := M) hz (by simpa only [Work.FTS.EllipticEst.Q0] using hY)
      (fun s θ hs h0 h1 => hbd s (by simp only [Set.mem_Ioi]; linarith [hz, hs.1]) θ ⟨h0, h1⟩)
    simpa only [← Work.Elliptic.Ktheta_eq_K] using h
  -- Rewrite the density as `(angular moment) / s` and divide by the continuous, nonvanishing `s`.
  have hfun : (fun s => (∫ θ in Work.Spaces.Iθ, Work.Spaces.K θ * Y s θ) / s)
      = Work.FM.L12dens Work.Spaces.K Y :=
    funext fun s => (L12dens_eq_thetaIntegral_div Y s).symm
  rw [← hfun]
  exact hQang.div continuousAt_id (ne_of_gt hz)

end Work.FTS.StrongEps.E5Aux2.L12FtauAux
