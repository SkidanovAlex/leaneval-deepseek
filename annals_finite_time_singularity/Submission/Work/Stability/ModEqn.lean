import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Complex.Trigonometric
import Submission.Work.Stability.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.Stability

set_option autoImplicit false
set_option linter.unusedSimpArgs false

/-! ## The hypotheses of the derivation -/

/-- **The derivation data for the dynamical `g`-equation.**  This bundles the hypotheses that
the Construction area's derivation of `(intermediategeqn)` takes as inputs (its `h2,h3,h5,h6`,
`hDz`, `hpth`, `hL`), now *for the family* `F(·,·,s) = F_* + g(·,·,s)`:

* `h2`, `h3` — the decomposition `Φ = Φ̃ + Θ` is differentiable in `z` and `θ` (with the
  derivatives of `Θ` computed separately);
* `h5`, `h6` — the two derivative evaluations of `Θ = (1/(4α))sin(2θ)L₁₂(F)`, supplied by
  `Work.Construction.pth_Theta_eq` and `Work.Construction.Dz_Theta_eq` (see
  `Work.Stability.ThetaPthFtot`, `Work.Stability.ThetaPzFtot`);

(the four `Φ = Φ̃ + Θ` fields `h2, h3, h5, h6` are restricted to the **open quadrant** `Qd`:
`h5` genuinely needs `z > 0`, since `L₁₂(F_*)` is a Lean-junk `0` for `z ≤ -1` while
`FK(F_*) ≠ 0` there — see the reviewer's counterexample.  `DynGEquation` only consumes them on
`Qd`, where its conclusion lives.)
* `hDz`, `hpth` — the splitting of `D_z` and `∂_θ` over `F = F_* + g` on the *open quadrant*
  (where `z > 0` and `0 < θ < π/2`, so both `F_*`-slices are differentiable), supplied by
  `Work.Stability.PzFstarAdd` / `PthFstarAdd` from differentiability of the slices of `g`;
* `hL` — the splitting of `L₁₂` over `F = F_* + g`, supplied by integrability of the
  `L₁₂`-densities (`Work.Stability.L12Add`). -/
structure GDerivData (α : ℝ) (g φ : F3) : Prop where
  h2 : ∀ z θ s, (z, θ) ∈ Work.Construction.Qd →
      Work.Spaces.pz (slice φ s) z θ
        = Work.Spaces.pz (Work.Construction.PhiTil α (Ftot α g s) (slice φ s)) z θ
          + Work.Spaces.pz (Work.Construction.Theta α (Ftot α g s)) z θ
  h3 : ∀ z θ s, (z, θ) ∈ Work.Construction.Qd →
      Work.Spaces.pth (slice φ s) z θ
        = Work.Spaces.pth (Work.Construction.PhiTil α (Ftot α g s) (slice φ s)) z θ
          + Work.Spaces.pth (Work.Construction.Theta α (Ftot α g s)) z θ
  h5 : ∀ z θ s, (z, θ) ∈ Work.Construction.Qd →
      z * Work.Spaces.pz (Work.Construction.Theta α (Ftot α g s)) z θ
        = -(1 / (4 * α)) * Work.Construction.s2 θ * Work.Construction.FK (Ftot α g s) z
  h6 : ∀ z θ s, (z, θ) ∈ Work.Construction.Qd →
      Work.Spaces.pth (Work.Construction.Theta α (Ftot α g s)) z θ
        = (1 / (2 * α)) * Real.cos (2 * θ) * Work.Construction.L12 (Ftot α g s) z
  hDz : ∀ z θ s, (z, θ) ∈ Work.Construction.Qd →
      Work.Spaces.Dz (fun z θ => Ftot α g s z θ) z θ
        = Work.Spaces.Dz (Work.Construction.Fstar α) z θ + Work.Spaces.Dz (slice g s) z θ
  hpth : ∀ z θ s, (z, θ) ∈ Work.Construction.Qd →
      Work.Spaces.pth (fun z θ => Ftot α g s z θ) z θ
        = Work.Spaces.pth (Work.Construction.Fstar α) z θ + Work.Spaces.pth (slice g s) z θ
  hL : ∀ z s, Work.Construction.L12 (fun z θ => Ftot α g s z θ) z
      = Work.Construction.L12 (Work.Construction.Fstar α) z + Work.Construction.L12 (slice g s) z

/-! ## The modulated form of the `g`-equation -/




/-! ## The modulation conditions -/




end Work.Stability
