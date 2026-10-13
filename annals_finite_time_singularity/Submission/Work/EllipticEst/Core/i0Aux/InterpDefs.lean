/-
Copyright: work module for the Elgindi finite-time singularity project.

# The single-function mixed-derivative interpolation: the two forms of the statement

* `InterpStrip` — the estimate for `G` which is `C^∞` on the *open strip*
  `(0,∞) × (-1, π/2+1)`.  This is the class in which the angular slices `θ ↦ D_zG z θ` are `C²`
  on the closed interval `[0,π/2]`, which is what the one-dimensional angular estimates of the
  workspace (`Work.FTS.EllipticEst.Alpha4.slice_key`, `Work.EllipticEst.Core.thetaAgmonCompact`,
  `Work.FTS.EllipticEst.ThetaU.ang_ibp_eta`) need.

* `InterpOpen` — the estimate for the class `Work.FTS.EllipticEst.SmoothOpen` (smooth on the
  *open* quadrant only) occurring in the statements of the chapter.

Both are the paper's §7 interpolation estimate

  `α² ∫∫ (D_z∂_θG)² w² σ_η ≤ C (α⁴ ∫∫ (D_z²G)² w² σ_η + ∫∫ (∂_θθG)² w² σ_η
                              + α² ∫∫ (D_zG)² w² σ_η)`,  `σ_η = sin(2θ)^{-η}`,

written with the slice functionals `mixIntS`, `ddIntS`, `ttIntS`, `dIntS` of
`Submission/Work/EllipticEst/Core/Defs.lean`.
-/
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.Spaces.Defs
import Submission.Work.EllipticEst.Core.Defs
import Submission.Work.FTS.EllipticEst.OpenQDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.EllipticEst.Core.i0Aux

set_option autoImplicit false

/-- The interpolation inequality of `Core/Defs` with constant `C`, for the *strip* class: `G` is
`C^∞` on `(0,∞) × (-1, π/2+1)`.  The four `IntegrableOn` hypotheses make the four slice
functionals honest, so that the displayed Bochner integrals are the genuine values. -/
def InterpStrip (C : ℝ) : Prop :=
  ∀ (α : ℝ) (G : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 / 4 →
    (∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry G)
      (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-1 : ℝ) (Real.pi / 2 + 1))) →
    (∀ z : ℝ, G z 0 = 0) → (∀ z : ℝ, G z (Real.pi / 2) = 0) →
    MeasureTheory.IntegrableOn (fun z : ℝ => Work.EllipticEst.Core.mixIntS G z) Work.Spaces.Iz →
    MeasureTheory.IntegrableOn (fun z : ℝ => Work.EllipticEst.Core.ddIntS G z) Work.Spaces.Iz →
    MeasureTheory.IntegrableOn (fun z : ℝ => Work.EllipticEst.Core.ttIntS G z) Work.Spaces.Iz →
    MeasureTheory.IntegrableOn (fun z : ℝ => Work.EllipticEst.Core.dIntS G z) Work.Spaces.Iz →
    α ^ 2 * (∫ z in Work.Spaces.Iz, Work.EllipticEst.Core.mixIntS G z)
      ≤ C * (α ^ 4 * (∫ z in Work.Spaces.Iz, Work.EllipticEst.Core.ddIntS G z)
          + (∫ z in Work.Spaces.Iz, Work.EllipticEst.Core.ttIntS G z)
          + α ^ 2 * (∫ z in Work.Spaces.Iz, Work.EllipticEst.Core.dIntS G z))

/-- **Slicewise honesty of the three right-hand side functionals** for `z > 0`: each of the three
angular slice integrands is integrable against `σ_η = sin(2θ)^{-η}`.  This is what rules out the
*junk-value* case (`¬ Integrable` ⟹ the Bochner integral is `0`), in which the weaker
hypothesis `IntegrableOn (fun z => ttIntS G z) Iz` would be satisfied by the function `0` while
the corresponding slice integral diverges.

Under this hypothesis the slice functionals are honest and the three Bochner integrals in the
statement below are the genuine values. -/
def SliceHonestOpen (G : ℝ → ℝ → ℝ) : Prop :=
  (∀ z : ℝ, 0 < z → MeasureTheory.IntegrableOn (fun θ : ℝ =>
      (Work.Spaces.pth (Work.Spaces.pth G) z θ) ^ 2 * (Work.Spaces.w z) ^ 2
        * Work.FTS.EllipticEst.thEta θ) Work.Spaces.Iθ) ∧
  (∀ z : ℝ, 0 < z → MeasureTheory.IntegrableOn (fun θ : ℝ =>
      (Work.Spaces.Dz (Work.Spaces.Dz G) z θ) ^ 2 * (Work.Spaces.w z) ^ 2
        * Work.FTS.EllipticEst.thEta θ) Work.Spaces.Iθ) ∧
  (∀ z : ℝ, 0 < z → MeasureTheory.IntegrableOn (fun θ : ℝ =>
      (Work.Spaces.Dz G z θ) ^ 2 * (Work.Spaces.w z) ^ 2 * Work.FTS.EllipticEst.thEta θ)
    Work.Spaces.Iθ)

/-- The interpolation inequality of `Core/Defs` with constant `C`, for the *open* class
`Work.FTS.EllipticEst.SmoothOpen`. -/
def InterpOpen (C : ℝ) : Prop :=
  ∀ (α : ℝ) (G : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 / 4 →
    Work.FTS.EllipticEst.SmoothOpen G →
    (∀ z : ℝ, G z 0 = 0) → (∀ z : ℝ, G z (Real.pi / 2) = 0) →
    SliceHonestOpen G →
    MeasureTheory.IntegrableOn (fun z : ℝ => Work.EllipticEst.Core.mixIntS G z) Work.Spaces.Iz →
    MeasureTheory.IntegrableOn (fun z : ℝ => Work.EllipticEst.Core.ddIntS G z) Work.Spaces.Iz →
    MeasureTheory.IntegrableOn (fun z : ℝ => Work.EllipticEst.Core.ttIntS G z) Work.Spaces.Iz →
    MeasureTheory.IntegrableOn (fun z : ℝ => Work.EllipticEst.Core.dIntS G z) Work.Spaces.Iz →
    α ^ 2 * (∫ z in Work.Spaces.Iz, Work.EllipticEst.Core.mixIntS G z)
      ≤ C * (α ^ 4 * (∫ z in Work.Spaces.Iz, Work.EllipticEst.Core.ddIntS G z)
          + (∫ z in Work.Spaces.Iz, Work.EllipticEst.Core.ttIntS G z)
          + α ^ 2 * (∫ z in Work.Spaces.Iz, Work.EllipticEst.Core.dIntS G z))

end Work.EllipticEst.Core.i0Aux
