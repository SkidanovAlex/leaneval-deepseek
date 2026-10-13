/-
# `H5/AngRad5/Engine5` — the *statement* of the level-`5` angular-`×`-radial engine

This file only fixes the interface used by three parallel developments of the level-`5`
`N`-block chapter:

* `AngRadHkMem5` (module `Submission.Work.FTS.StrongEps.H5.AngRad5.AngRadHkMem5`) proves
  `AngRadEngine5`;
* the level-`5` scaled-`F_*`-atoms (`H5.Atoms.StarAtomsScaled5`) and the level-`5`
  `FK`-products (`H5.Atoms.StarAtomsFK5`) consume `AngRadEngine5` as a hypothesis.

The engine is the level-`5` transcription of the level-`4` pair
`Work.FTS.Nonlinear.Open.AngRadHkMem` (membership) `+`
`Work.FTS.Nonlinear.Pieces.RNP.Xn_ang_rad_le_gen` (norm bound), packaged as
`Work.FTS.StrongEps.ClassCRHS.atom_hk`:  for a separable product `(z,θ) ↦ a θ · r z` of a
`θ`-only profile `a` with the pointwise slot bounds
`|a θ| ≤ B0`, `|D_θ^i a| ≤ B1·G θ` (`1 ≤ i ≤ 5`) and a radial profile `r` whose lift is
`ℋ⁵`-honest with `HkNorm α 5 (r-lift) ≤ Crad`, the product is `ℋ⁵`-honest and

`HkNorm α 5 (a·r) ≤ C · √(B0² · 10⁴ + 5 · B1² · M) · Crad`,   `M ≥ ∫_θ G² · sin(2θ)^{-γ}`.

The pointwise input is `H5.AngRad5.HkIntegrand_ang_rad_le5`; the angular mass integral
`∫ G² smG` is the `M` of the hypothesis; the constant `5` (the number of angular orders
`1..5`) replaces the `4` of the level-`4` statement, matching `H5.AngFac5.ang_fac5_integrable_bound`.
-/
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.StrongEps.H5.AngRad5.HkIntegrand_ang_rad_le5
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.Nonlinear.RadialProd.radial_prod

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.H5.AngRad5

set_option autoImplicit false

/-- **The level-`5` angular-`×`-radial engine** (see the module docstring). -/
def AngRadEngine5 : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ {α : ℝ}, 0 < α → α ≤ 1 →
    ∀ {a r G : ℝ → ℝ} {B0 B1 M Crad : ℝ},
      Work.FTS.EllipticEst.SmoothOpen (fun _ (θ : ℝ) => a θ) →
      Work.FTS.EllipticEst.SmoothOpen (fun z (_ : ℝ) => r z) →
      (∀ θ ∈ Work.Spaces.Iθ, 0 ≤ G θ) →
      MeasureTheory.IntegrableOn
        (fun θ : ℝ => G θ ^ 2 * Work.FTS.Nonlinear.RadialProd.smG α θ) Work.Spaces.Iθ →
      0 ≤ B0 → 0 ≤ B1 → 0 ≤ M → 0 ≤ Crad →
      (∀ θ ∈ Work.Spaces.Iθ, |a θ| ≤ B0) →
      (∀ i : ℕ, 1 ≤ i → i ≤ 5 → ∀ θ ∈ Work.Spaces.Iθ,
        |Work.Spaces.DthIter i (fun _ (θ' : ℝ) => a θ') 0 θ| ≤ B1 * G θ) →
      (∫ θ in Work.Spaces.Iθ, G θ ^ 2 * Work.FTS.Nonlinear.RadialProd.smG α θ ≤ M) →
      Work.Spaces.HkMem α 5 (fun z (_ : ℝ) => r z) →
      Work.Spaces.HkNorm α 5 (fun z (_ : ℝ) => r z) ≤ Crad →
      Work.Spaces.HkMem α 5 (fun z θ => a θ * r z) ∧
      Work.Spaces.HkNorm α 5 (fun z θ => a θ * r z)
        ≤ C * Real.sqrt (B0 ^ 2 * 10 ^ 4 + 5 * B1 ^ 2 * M) * Crad

end Work.FTS.StrongEps.H5.AngRad5
