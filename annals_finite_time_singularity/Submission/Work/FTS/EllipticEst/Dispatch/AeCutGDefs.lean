/-
Copyright: work module for the Elgindi finite-time singularity project.

# `Dispatch/AeCutGDefs` — the vocabulary of the truncated `w²`-energy inequality with a
general radial cut-off

This module fixes the notation for the proof of the truncated `w²`-weighted energy inequality
of Step 1 of Elgindi's `prop:H2` in the almost-everywhere class
`Work.FTS.EllipticEst.H2W.Ae.AeData`, *for a general* `C²` cut-off `χ` (rather than the
specific family `cut n` used by `Dispatch/aeSigmaEnergyMach`).

For a cut-off `χ` and data `u, G` we write `W = Wcut χ = χ·w²` and, for `θ ∈ (0,π/2)`,
the six `z`-functionals

* `TA  χ u θ = ∫_z W(z)·(z ∂_z u(z,θ))²`,
* `TBg χ u θ = ∫_z W(z)·z² ∂_z²u(z,θ)·u(z,θ)`,
* `TDg χ u θ = ∫_z W(z)·z ∂_zu(z,θ)·u(z,θ)`,
* `TIg χ u G θ = ∫_z W(z)·G(z,θ)·u(z,θ)`,
* `TKg χ u θ = ∫_z W(z)·L₀u(z,θ)·u(z,θ)`,
* `TGg χ u θ = ½∫_z (z²W)''(z)·u(z,θ)²`,
* `TEg χ u θ = -½∫_z (zW)'(z)·u(z,θ)²`,

together with the two truncation-error kernels

* `F1g χ z = |χ'(z)|·(z w(z)²)`,
* `F2g χ z = 2|χ'(z)|·|(z²w²)'(z)| + |χ''(z)|·(z²w(z)²)`.

The two per-angle integration-by-parts identities of the truncated energy identity read

`TBg = TGg - TA` and `TDg = TEg`,

and the weight algebra gives `(z²W)'' ≤ 6W + F2g`, `(zW)' ≥ -3W - F1g` on `z > 0`.
-/
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.EllipticEst.H2W.Ae.Defs
import Submission.Work.FTS.EllipticEst.Dispatch.aeFirstEnergyDTools
import Submission.Work.FTS.EllipticEst.Dispatch.sliceZibpD
import Submission.Work.FTS.EllipticEst.weight_algebra_fts

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology ENNReal
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.Dispatch.AeCut

set_option autoImplicit false
set_option linter.unusedVariables false

/-- The `z`-functional `∫_z W(z)(z ∂_zu(z,θ))²` of the truncated energy identity. -/
def TA (χ : ℝ → ℝ) (u : ℝ → ℝ → ℝ) (θ : ℝ) : ℝ :=
  ∫ z in Set.Ioi (0 : ℝ), Wcut χ z * (z * Work.Spaces.pz u z θ) ^ 2

/-- The `z`-functional `∫_z W(z) z² ∂_z²u(z,θ) u(z,θ)`. -/
def TBg (χ : ℝ → ℝ) (u : ℝ → ℝ → ℝ) (θ : ℝ) : ℝ :=
  ∫ z in Set.Ioi (0 : ℝ), Wcut χ z * z ^ 2 * Work.Spaces.pzIter 2 u z θ * u z θ

/-- The `z`-functional `∫_z W(z) z ∂_zu(z,θ) u(z,θ)`. -/
def TDg (χ : ℝ → ℝ) (u : ℝ → ℝ → ℝ) (θ : ℝ) : ℝ :=
  ∫ z in Set.Ioi (0 : ℝ), Wcut χ z * (z * Work.Spaces.pz u z θ) * u z θ

/-- The pairing `∫_z W(z) G(z,θ) u(z,θ)` with the source. -/
def TIg (χ : ℝ → ℝ) (u G : ℝ → ℝ → ℝ) (θ : ℝ) : ℝ :=
  ∫ z in Set.Ioi (0 : ℝ), Wcut χ z * (G z θ * u z θ)

/-- The pairing `∫_z W(z) L₀u(z,θ) u(z,θ)` with the angular operator. -/
def TKg (χ : ℝ → ℝ) (u : ℝ → ℝ → ℝ) (θ : ℝ) : ℝ :=
  ∫ z in Set.Ioi (0 : ℝ), Wcut χ z * (Work.Elliptic.Lzero u z θ * u z θ)

/-- The weight term `½∫_z (z²W)''(z) u(z,θ)²` of the second integration by parts. -/
def TGg (χ : ℝ → ℝ) (u : ℝ → ℝ → ℝ) (θ : ℝ) : ℝ :=
  1 / 2 * ∫ z in Set.Ioi (0 : ℝ),
    deriv (deriv (fun z => z ^ 2 * Wcut χ z)) z * (u z θ) ^ 2

/-- The weight term `-½∫_z (zW)'(z) u(z,θ)²` of the first integration by parts. -/
def TEg (χ : ℝ → ℝ) (u : ℝ → ℝ → ℝ) (θ : ℝ) : ℝ :=
  -(1 / 2 * ∫ z in Set.Ioi (0 : ℝ),
    deriv (fun z => z * Wcut χ z) z * (u z θ) ^ 2)

/-- The first truncation-error kernel `|χ'|·(z w²)`. -/
def F1g (χ : ℝ → ℝ) (z : ℝ) : ℝ := |deriv χ z| * (z * (Work.Spaces.w z) ^ 2)

/-- The second truncation-error kernel `2|χ'|·|(z²w²)'| + |χ''|·(z²w²)`. -/
def F2g (χ : ℝ → ℝ) (z : ℝ) : ℝ :=
  2 * |deriv χ z| * |deriv (fun y => y ^ 2 * (Work.Spaces.w y) ^ 2) z|
    + |deriv (deriv χ) z| * (z ^ 2 * (Work.Spaces.w z) ^ 2)

end Work.FTS.EllipticEst.Dispatch.AeCut
