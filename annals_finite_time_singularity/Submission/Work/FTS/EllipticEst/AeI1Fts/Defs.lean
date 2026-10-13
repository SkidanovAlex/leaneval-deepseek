import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Submission.Work.FTS.EllipticEst.H2W.Ae.Defs
import Submission.Work.FTS.EllipticEst.AngSecond.Defs
import Submission.Work.FTS.EllipticEst.AngSecond.I1_defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `AeI1Fts/Defs` — the vocabulary of the `I₁` bound in the weak class `AeData`

Notation of `Submission/Work/FTS/EllipticEst/AeI1Fts/I1Paper_mixed.lean`: with `u` a datum
smooth on the open quadrant `(0,∞) × (0,π/2)`,

* `U u = z ∂_z u` (definitionally `H2W.Ae.grad u`),
* `V u = z ∂_z ∂_θ u` (the mixed first-order slot whose `ℋ⁰`-honesty is the extra hypothesis
  of `I1Paper_mixed`),
* `Hh u = z ∂_z ∂_θθ u = ∂_θθ (U u)`,
* `AA u = z² ∂_zz u` (definitionally `H2W.Ae.rad2 u`), `BB u = ∂_θθ u`
  (definitionally `H2W.Ae.ang2 u`);
* the angular weights `σ = sigE = sin(2θ)^{-η}`, `σ₁ = sig1 = sin(2θ)^{-1-η}`,
  `σ₂ = sig2 = sin(2θ)^{-2-η}` with `η = Work.Spaces.eta = 99/100`;
* `thCut δ` is the pointwise angular cut-off `χ(2θ/δ)·χ(2(π/2-θ)/δ)`;
* `Fp u` is the `z`-integrand of the pointwise identity `(†)`
  `w²(A·B + cw·U·B + U·H) = ∂_z(z·U·B·w²)`, and `Fd u z θ = z·U·B·w²` is its primitive in `z`.

No proof is carried out here: this module only fixes the vocabulary shared by the target
`I1Paper_mixed` and the auxiliary lemmas it is assembled from.
-/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.AeI1Fts

set_option autoImplicit false

/-- `U = z ∂_z u`. -/
def U (u : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ := fun z θ => z * Work.Spaces.pz u z θ

/-- `V = z ∂_z ∂_θ u` (the mixed first-order slot). -/
def V (u : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ :=
  fun z θ => z * Work.Spaces.pz (Work.Spaces.pth u) z θ

/-- `H = z ∂_z ∂_θθ u = ∂_θθ U`. -/
def Hh (u : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ :=
  fun z θ => z * Work.Spaces.pz (Work.Spaces.pthIter 2 u) z θ

/-- `A = z² ∂_zz u`. -/
def AA (u : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ := fun z θ => z ^ 2 * Work.Spaces.pzIter 2 u z θ

/-- `B = ∂_θθ u`. -/
def BB (u : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ := Work.Spaces.pthIter 2 u

/-- `σ θ = sin(2θ)^{-η}`. -/
def sigE (θ : ℝ) : ℝ := (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))

/-- `σ₁ θ = sin(2θ)^{-1-η}`. -/
def sig1 (θ : ℝ) : ℝ := (Real.sin (2 * θ)) ^ (-(1 + Work.Spaces.eta))

/-- `σ₂ θ = sin(2θ)^{-2-η}`. -/
def sig2 (θ : ℝ) : ℝ := (Real.sin (2 * θ)) ^ (-(2 + Work.Spaces.eta))

/-- The open angular interval. -/
def Iθo : Set ℝ := Set.Ioo 0 (Real.pi / 2)

/-- The open quadrant. -/
def qd : Set (ℝ × ℝ) := Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)

/-- The pointwise angular cut-off `ψ_δ(θ) = χ(2θ/δ)·χ(2(π/2-θ)/δ)`, equal to `1` on
`[δ/2, π/2-δ/2]` and supported in `(0,π/2)`. -/
def thCut (δ θ : ℝ) : ℝ :=
  Real.smoothTransition (2 * θ / δ) * Real.smoothTransition (2 * (Real.pi / 2 - θ) / δ)

/-- The pointwise `z`-integrand of the `(†)`-identity. -/
def Fp (u : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ := fun z θ =>
  (z ^ 2 * Work.Spaces.pzIter 2 u z θ) * Work.Spaces.pthIter 2 u z θ
    + Work.FTS.EllipticEst.AngSecond.cw z * (z * Work.Spaces.pz u z θ)
        * Work.Spaces.pthIter 2 u z θ
    + (z * Work.Spaces.pz u z θ) * (z * Work.Spaces.pz (Work.Spaces.pthIter 2 u) z θ)

/-- The pointwise `z`-integrand whose derivative is `w²·Fp`. -/
def Fd (u : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ := fun z θ =>
  z * (z * Work.Spaces.pz u z θ) * Work.Spaces.pthIter 2 u z θ * (Work.Spaces.w z) ^ 2

end Work.FTS.EllipticEst.AeI1Fts
