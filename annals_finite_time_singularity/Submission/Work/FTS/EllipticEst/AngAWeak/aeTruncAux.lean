import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.StraightDefs
import Submission.Work.FTS.EllipticEst.H2W.Ae.Defs
import Submission.Work.Elliptic.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# Auxiliary quantities for `aeTruncIdent`

The radial `z`-integration by parts of the truncated energy identity is carried out slice by
slice in `θ`; the analytic inputs of the weak class (`AeData`) are three weighted angular
masses of a slice and their pointwise bounds.

* `AAA u z = ∫_θ (∂_θθu(z,·))² · sin(2θ)^{-η}` — the angular `H²`-mass of the slice
  (`HkIntegrand α 0 (pthIter 2 u) = w z ^ 2 * AAA u z` on `Iθ`, so the `AeData`-hypothesis
  `HkMem α 0 (pthIter 2 u)` says exactly that `z ↦ (w z)^2 * AAA u z` is integrable on `Iz`);
* `BBB u z = ∫_θ (z²∂_zzu(z,·))² · sin(2θ)^{-η}` — the same for the radial second derivative;
* `GGG G z = ∫_θ (G(z,·))² · sin(2θ)^{-η}` — the angular mass of the source.

The two `AeData`-hypotheses `HkMem α 0 (fun z θ => z^2 * pzIter 2 u z θ)` and
`HkMem α 0 G` are the corresponding `z`-integrability statements for `(w z)^2 * BBB u z` and
`(w z)^2 * GGG G z`.
-/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.AngAWeak

set_option autoImplicit false

/-- The angular `H²`-mass of the `θ`-slice: `AAA u z = ∫_θ (∂_θθu)² sin(2θ)^{-η}`. -/
def AAA (u : ℝ → ℝ → ℝ) (z : ℝ) : ℝ :=
  ∫ θ in Work.Spaces.Iθ, (Work.Spaces.pthIter 2 u z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ

/-- The angular mass of the radial second derivative of the slice:
`BBB u z = ∫_θ (z²∂_zzu)² sin(2θ)^{-η}`. -/
def BBB (u : ℝ → ℝ → ℝ) (z : ℝ) : ℝ :=
  ∫ θ in Work.Spaces.Iθ, (z ^ 2 * Work.Spaces.pzIter 2 u z θ) ^ 2
    * Work.FTS.EllipticEst.sEta θ

/-- The angular mass of the source: `GGG G z = ∫_θ G² sin(2θ)^{-η}`. -/
def GGG (G : ℝ → ℝ → ℝ) (z : ℝ) : ℝ :=
  ∫ θ in Work.Spaces.Iθ, (G z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ

/-- The angular measure against which the `z`-integration by parts is performed slicewise:
`sin(2θ)^{-η}` on `Iθ`. -/
def eθ (θ : ℝ) : ℝ := Work.FTS.EllipticEst.sEta θ

end Work.FTS.EllipticEst.AngAWeak
