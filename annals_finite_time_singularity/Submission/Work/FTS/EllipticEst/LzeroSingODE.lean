import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS.EllipticEst.LzeroSingDefs
import Submission.Work.FTS.EllipticEst.LzeroSingAuxDefs
import Submission.Work.FTS.EllipticEst.LzeroSingAuxDeriv
import Submission.Work.FTS.EllipticEst.LzeroSingAuxDeriv2
import Submission.Work.FTS.EllipticEst.LzeroAux.sin_mul_integrand
import Submission.Work.FTS.EllipticEst.LzeroAux.ode_algebra

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst

/-- `LzeroSing θ = sin(2θ) · ∫_{π/4}^{π/2-θ} ds/(sin s · sin(2s)²)` solves the angular
equation `-y'' + (tan · y)' - 6y = 0` on `(0, π/2)`.

The derivative computation is: with `F = SingInt` (so `SingInt' = -LzeroSingIntegrand (π/2-·)` and
`sin(2θ)·LzeroSingIntegrand (π/2-θ) = 1/(cos θ · sin 2θ)`),
`deriv LzeroSing θ = 2cos(2θ)·F(θ) - 1/(cos θ sin 2θ) = SingY1 θ` and
`deriv (deriv LzeroSing) θ = -4 sin(2θ)·F(θ) - sin θ/(cos²θ sin 2θ) = SingY2 θ`;
the remaining identity is the algebraic lemma `ode_algebra`. -/
theorem LzeroSingODE : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
    -(deriv (deriv Work.FTS.EllipticEst.LzeroSing) θ)
      + deriv (fun τ => Real.tan τ * Work.FTS.EllipticEst.LzeroSing τ) θ
      - 6 * Work.FTS.EllipticEst.LzeroSing θ = 0 := by
  intro θ hθ
  have hθ0 : 0 < θ := hθ.1
  have hθπ : θ < Real.pi / 2 := hθ.2
  have hcos_pos : 0 < Real.cos θ := Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hθπ⟩
  have hcos_ne : Real.cos θ ≠ 0 := ne_of_gt hcos_pos
  -- `LzeroSing` has derivative `SingY1` throughout `(0, π/2)`.
  have hLS_at : ∀ τ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), HasDerivAt LzeroSing (SingY1 τ) τ := by
    intro τ hτ
    have hsin : HasDerivAt (fun t : ℝ => Real.sin (2 * t)) (2 * Real.cos (2 * τ)) τ := by
      have h2 : HasDerivAt (fun t : ℝ => (2 : ℝ) * t) 2 τ := by
        simpa only [id_eq, mul_one] using (hasDerivAt_id τ).const_mul 2
      exact ((Real.hasDerivAt_sin (2 * τ)).comp τ h2).congr_deriv (by ring)
    have hint : HasDerivAt SingInt (-(LzeroSingIntegrand (Real.pi / 2 - τ))) τ :=
      SingInt_hasDerivAt τ hτ
    have hval : 2 * Real.cos (2 * τ) * SingInt τ
        + Real.sin (2 * τ) * (-(LzeroSingIntegrand (Real.pi / 2 - τ))) = SingY1 τ := by
      rw [SingY1_apply, ← LzeroAux.sin_mul_integrand τ hτ]
      ring
    have hprod : HasDerivAt (fun t : ℝ => Real.sin (2 * t) * SingInt t) (SingY1 τ) τ :=
      (hsin.mul hint).congr_deriv hval
    exact hprod
  -- hence `deriv LzeroSing =ᶠ SingY1` near `θ`, and `deriv (deriv LzeroSing) θ = SingY2 θ`.
  have hev : deriv LzeroSing =ᶠ[𝓝 θ] SingY1 := by
    filter_upwards [isOpen_Ioo.mem_nhds hθ] with τ hτ
    exact (hLS_at τ hτ).deriv
  have h2 : deriv (deriv LzeroSing) θ = SingY2 θ := by
    rw [Filter.EventuallyEq.deriv_eq hev, (SingY1_hasDerivAt_self θ hθ).deriv]
  have h3 : deriv (fun τ => Real.tan τ * LzeroSing τ) θ
      = (1 / Real.cos θ ^ 2) * LzeroSing θ + Real.tan θ * SingY1 θ :=
    ((Real.hasDerivAt_tan hcos_ne).mul (hLS_at θ hθ)).deriv
  rw [h2, h3, LzeroSing_eq_sin_mul_SingInt, SingY1_apply, SingY2_apply]
  exact LzeroAux.ode_algebra θ hθ (SingInt θ)

end Work.FTS.EllipticEst
