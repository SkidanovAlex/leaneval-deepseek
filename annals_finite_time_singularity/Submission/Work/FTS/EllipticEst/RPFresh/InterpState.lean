/-
Copyright: work module for the Elgindi finite-time singularity project.

# The two forms of the single-function mixed-derivative interpolation

This module contains only *definitions* (no proofs), so that the two analytic statements
they name can be proved in modules that do not inherit `sorryAx` from anywhere.

The paper's §7 interpolation estimate is

  `α² ∫∫ (D_z∂_θG)² w² σ_η ≤ C (α⁴ ∫∫ (D_z²G)² w² σ_η + ∫∫ (∂_θθG)² w² σ_η
                              + α² ∫∫ (D_zG)² w² σ_η)`,  `σ_η = sin(2θ)^{-η}`,

written with the slice functionals `mixIntS`, `ddIntS`, `ttIntS`, `dIntS` of
`Submission/Work/EllipticEst/Core/Defs.lean`, i.e.

  `α² ∫_z mixIntS G z ≤ C (α⁴ ∫_z ddIntS G z + ∫_z ttIntS G z + α² ∫_z dIntS G z)`.

* `InterpBox C` — the estimate with constant `C` for `G` smooth on the open quadrant and
  *supported in a compact box* `[a,b] × [a',b']` strictly inside the open quadrant.  In that
  case both the angular Agmon inequality and the radial integration by parts are
  unconditional (no boundary terms), and the estimate follows from the already proved
  `Work.EllipticEst.Core.thetaAgmonCompact` (slicewise in `z`) and
  `Work.EllipticEst.Core.radialIBP` (slicewise in `θ`) plus a weighted AM–GM.
  The proof is written out in `Submission/Work/EllipticEst/Core/interpBox.lean`
  (theorem `Work.EllipticEst.Core.interpBox`, same statement modulo the wrapper `InterpBox`),
  but that file does **not** compile: `η` is an unknown identifier there (the file is under
  `set_option autoImplicit false` and never declares a notation for it — add
  `local notation "η" => Work.Spaces.eta` right after the imports), and about fifteen
  further errors remain.  A copy of that file with the notation inserted is
  `_ib_fix.lean` in the workspace root and its error log is `_ib_fix.log`.

* `Work.EllipticEst.Core.i0Aux.InterpOpen C` (defined in
  `Submission/Work/EllipticEst/Core/i0Aux/InterpDefs.lean`) — the same estimate for
  `G : SmoothOpen` (smooth on the *open* quadrant only), with `G z 0 = G z (π/2) = 0` and
  the four functionals honest.
-/
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.EllipticEst.Core.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.RPFresh

set_option autoImplicit false

/-- **The compactly supported case of the mixed-derivative interpolation.**  `InterpBox C`
is the interpolation estimate of the paper's §7 with constant `C`, for functions `u` which
are `C^∞` on the open quadrant and vanish outside a compact box `[a,b] × [a',b']` contained
in the open quadrant (`0 < a < b`, `0 < a' < b' < π/2`). -/
def InterpBox (C : ℝ) : Prop :=
  ∀ (α : ℝ) (u : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 / 4 →
    Work.FTS.EllipticEst.SmoothOpen u →
    (∃ a b a' b' : ℝ, 0 < a ∧ a < b ∧ 0 < a' ∧ a' < b' ∧ b' < Real.pi / 2 ∧
      (∀ z θ : ℝ, z ∉ Set.Icc a b → u z θ = 0) ∧
      (∀ z θ : ℝ, θ ∉ Set.Icc a' b' → u z θ = 0)) →
    α ^ 2 * (∫ z in Work.Spaces.Iz, Work.EllipticEst.Core.mixIntS u z)
      ≤ C * (α ^ 4 * (∫ z in Work.Spaces.Iz, Work.EllipticEst.Core.ddIntS u z)
          + (∫ z in Work.Spaces.Iz, Work.EllipticEst.Core.ttIntS u z)
          + α ^ 2 * (∫ z in Work.Spaces.Iz, Work.EllipticEst.Core.dIntS u z))

end Work.FTS.EllipticEst.RPFresh
