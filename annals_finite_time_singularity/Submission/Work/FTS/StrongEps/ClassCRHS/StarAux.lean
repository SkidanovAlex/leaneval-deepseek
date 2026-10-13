/-
Copyright: work module for the Elgindi finite-time singularity project.

# The angular and radial profiles of the three scaled `F_*`-atoms

This module only fixes the *definitions* used by `StarAtomsScaled` and by the lemmas
proved for it in the sibling files of this directory:

* `SR0 z = 2z²/(1+z)³` and `SR2 z = 2z²(1-z)/(1+z)⁴`: the two radial profiles, smooth on
  `(0,∞)` with `D_z`-iterates of order `≤ 4` bounded by a constant times `z²/(1+z)³`;
* `SA0 α θ = αΓ(θ)/c(α)` and `SA1 α θ = α D_θΓ(θ)/c(α)`: the two angular profiles;
* `SGmj α θ = Γ(θ)(α + sin 2θ)`: the angular majorant against which the angular slots are
  bounded; its square against the weight `sin(2θ)^{-γ}` has a mass bound *uniform in*
  `0 < α ≤ 1` (`Work.FTS.Nonlinear.Pieces.RNP.gamWeightInt`).

The `ℋ⁴`-atoms themselves live in `Submission/Work/FTS/StrongEps/ClassCRHS/StarAtomsScaled.lean`.
-/
import Mathlib.Analysis.Complex.Trigonometric
import Submission.Work.Spaces.Defs
import Submission.Work.Spaces.GammaW_Prelim

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.ClassCRHS

set_option autoImplicit false

/-- The radial profile `z ↦ 2z²/(1+z)³` of the first two scaled `F_*`-atoms. -/
def SR0 (z : ℝ) : ℝ := 2 * z ^ 2 / (1 + z) ^ 3

/-- The radial profile `z ↦ 2z²(1-z)/(1+z)⁴` of the third scaled `F_*`-atom. -/
def SR2 (z : ℝ) : ℝ := 2 * z ^ 2 * (1 - z) / (1 + z) ^ 4

/-- The angular profile `αΓ/c` of `F_*`. -/
def SA0 (α θ : ℝ) : ℝ := α * Work.Spaces.Gam α θ / Work.Spaces.c α

/-- The angular profile `α D_θΓ/c` of `D_θF_*`. -/
def SA1 (α θ : ℝ) : ℝ :=
  α * Work.Spaces.dthU (fun t => Work.Spaces.Gam α t) θ / Work.Spaces.c α

/-- The angular majorant `Γ·(α + sin 2θ)`: `G²·sin(2θ)^{-γ}` has an `α`-uniform mass bound
(`Work.FTS.Nonlinear.Pieces.RNP.gamWeightInt`). -/
def SGmj (α θ : ℝ) : ℝ := Work.Spaces.Gam α θ * (α + Real.sin (2 * θ))

end Work.FTS.StrongEps.ClassCRHS
