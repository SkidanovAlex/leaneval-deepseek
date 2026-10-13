/-
Copyright: work module for the Elgindi finite-time singularity project.

# `AngAWeak/AeI1MixedDefs` — the vocabulary of the `I₁` bound with the mixed slot

This module fixes the objects of the proof of `Work.FTS.EllipticEst.AngAWeak.aeI1Mixed`, the
`I₁` lower bound of Step 2 of Elgindi's `prop:H2` (Annals **194** (2021)) in the
almost-everywhere class `H2W.Ae.AeData` **with the extra honesty of the mixed first-order slot**
`V = z ∂_z∂_θ u` (the second hypothesis of `aeI1Mixed`).

Notation (`u : ℝ → ℝ → ℝ` a datum, `σ θ = sin(2θ)^{-η}`, `σ₂ θ = sin(2θ)^{-(2+η)}`,
`η = Work.Spaces.eta = 99/100`, `w z = (1+z)²/z²`):

* `i1U u = z ∂_z u`   (the target's `IP`-slot `U`),
* `i1V u = z ∂_z ∂_θ u = ∂_θ (i1U u)`   (the extra slot `V`),
* `i1H u = z ∂_z ∂_θθ u = ∂_θθ (i1U u) = ∂_θ (i1V u)`,
* `i1Q u = z² ∂_z² u`,   `i1B u = ∂_θθ u`;

* `i1Zeta u z = ∫_θ σ θ · U z θ · B z θ`,   `i1q u z = ∫_θ σ θ · Q z θ · B z θ`,
* `i1t u χ θ = ∫_z χ z · w z² · U z θ · H z θ`   (the `θ`-outer `UH`-slice integral);

* `sliceFlux h θ = σ θ h θ h'(θ) + η cot(2θ) σ θ h(θ)²`   (the 1-D flux of a slice).

The three auxiliary lemmas the proof is assembled from are
`AngAWeak.aeI1SliceFlux` (the 1-D truncated flux inequality for a slice),
`AngAWeak.aeI1ZibpCut` (the radial integration by parts with the cut-off `cut n`, integrated in
`θ`) and `AngAWeak.aeI1HtermCut` (the upper bound of the `θ`-outer `UH`-term).
-/
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.EllipticEst.H2W.Ae.Defs
import Submission.Work.FTS.EllipticEst.AngSecond.Defs
import Submission.Work.FTS.EllipticEst.AeI1Fts.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.AngAWeak

set_option autoImplicit false

/-! ## The slots -/

/-- `U u = z ∂_z u` (definitionally `H2W.Ae.grad u`). -/
def i1U (u : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ := fun z θ => z * Work.Spaces.pz u z θ

/-- `V u = z ∂_z ∂_θ u = ∂_θ (U u)` (the extra slot of `aeI1Mixed`). -/
def i1V (u : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ := fun z θ => z * Work.Spaces.pz (Work.Spaces.pth u) z θ

/-- `H u = z ∂_z ∂_θθ u = ∂_θθ (U u) = ∂_θ (V u)`. -/
def i1H (u : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ :=
  fun z θ => z * Work.Spaces.pz (Work.Spaces.pthIter 2 u) z θ

/-- `Q u = z² ∂_z² u` (definitionally `H2W.Ae.rad2 u`). -/
def i1Q (u : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ := fun z θ => z ^ 2 * Work.Spaces.pzIter 2 u z θ

/-- `B u = ∂_θθ u` (definitionally `H2W.Ae.ang2 u`). -/
def i1B (u : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ := Work.Spaces.pthIter 2 u

theorem i1U_eq_grad (u : ℝ → ℝ → ℝ) : i1U u = Work.FTS.EllipticEst.H2W.Ae.grad u := rfl
theorem i1Q_eq_rad2 (u : ℝ → ℝ → ℝ) : i1Q u = Work.FTS.EllipticEst.H2W.Ae.rad2 u := rfl
theorem i1B_eq_ang2 (u : ℝ → ℝ → ℝ) : i1B u = Work.FTS.EllipticEst.H2W.Ae.ang2 u := rfl
theorem i1V_eq (u : ℝ → ℝ → ℝ) : i1V u = AeI1Fts.V u := rfl
theorem i1H_eq (u : ℝ → ℝ → ℝ) : i1H u = AeI1Fts.Hh u := rfl

/-! ## The angular weights (the tree's own `sig` / `sig2`) -/

/-- `σ θ = sin(2θ)^{-η}` (the tree's `AngSecond.sig`). -/
def i1Sig (θ : ℝ) : ℝ := (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))

/-- `σ₂ θ = sin(2θ)^{-(2+η)}` (the tree's `AeI1Fts.sig2`). -/
def i1Sig2 (θ : ℝ) : ℝ := (Real.sin (2 * θ)) ^ (-(2 + Work.Spaces.eta))

theorem i1Sig_eq_sig (θ : ℝ) : i1Sig θ = Work.FTS.EllipticEst.AngSecond.sig θ := rfl
theorem i1Sig2_eq_sig2 (θ : ℝ) : i1Sig2 θ = AeI1Fts.sig2 θ := rfl

/-! ## The 1-D slice flux -/

/-- The flux of a slice `h`: `Φ θ = σ θ · h θ · h'(θ) + η cot(2θ) σ θ · h(θ)²`. -/
def sliceFlux (h : ℝ → ℝ) (θ : ℝ) : ℝ :=
  i1Sig θ * h θ * deriv h θ + Work.Spaces.eta * Real.cot (2 * θ) * i1Sig θ * (h θ) ^ 2

/-! ## The `z`-slice integrals of the `θ`-outer bookkeeping -/

/-- `ζ(z) = ∫_θ σ θ · U z θ · B z θ`. -/
def i1Zeta (u : ℝ → ℝ → ℝ) (z : ℝ) : ℝ :=
  ∫ θ in Work.Spaces.Iθ, i1Sig θ * i1U u z θ * i1B u z θ

/-- `q(z) = ∫_θ σ θ · Q z θ · B z θ`. -/
def i1q (u : ℝ → ℝ → ℝ) (z : ℝ) : ℝ :=
  ∫ θ in Work.Spaces.Iθ, i1Sig θ * i1Q u z θ * i1B u z θ

/-- `t(χ, θ) = ∫_z χ z · w z² · U z θ · H z θ`. -/
def i1t (u : ℝ → ℝ → ℝ) (χ : ℝ → ℝ) (θ : ℝ) : ℝ :=
  ∫ z in Set.Ioi 0, χ z * (Work.Spaces.w z) ^ 2 * i1U u z θ * i1H u z θ

/-- `Aa(χ) = ∫_z χ z w z² ∫_θ σ θ · U z θ²`. -/
def i1Aa (u : ℝ → ℝ → ℝ) (χ : ℝ → ℝ) : ℝ :=
  ∫ z in Set.Ioi 0, χ z * (Work.Spaces.w z) ^ 2
    * ∫ θ in Work.Spaces.Iθ, i1Sig θ * (i1U u z θ) ^ 2

/-- `Pp(χ) = ∫_z χ z w z² ∫_θ σ θ · V z θ²`. -/
def i1Pp (u : ℝ → ℝ → ℝ) (χ : ℝ → ℝ) : ℝ :=
  ∫ z in Set.Ioi 0, χ z * (Work.Spaces.w z) ^ 2
    * ∫ θ in Work.Spaces.Iθ, i1Sig θ * (i1V u z θ) ^ 2

/-- `N(χ) = ∫_z χ z w z² ∫_θ cos²(2θ) σ₂ θ · U z θ²`. -/
def i1N (u : ℝ → ℝ → ℝ) (χ : ℝ → ℝ) : ℝ :=
  ∫ z in Set.Ioi 0, χ z * (Work.Spaces.w z) ^ 2
    * ∫ θ in Work.Spaces.Iθ, (Real.cos (2 * θ)) ^ 2 * i1Sig2 θ * (i1U u z θ) ^ 2

end Work.FTS.EllipticEst.AngAWeak
