/-
# `Work.FTS.StrongPersist.L3Rhs.N0gAuxDefs` — auxiliary vocabulary of `N0gCoupled`

The coupled half of the `L3RhsN0gBlock` estimate is about the product

  `Mf f · Bf α f = L₁₂(f)(z) · Bf α f z θ`,   `Bf α f = Vf α f + Vfs α`,

with `Mf f = (z,θ) ↦ L₁₂(f)(z)` radial and

  `Vf α f  = (1/α) f + (3/(2α)) sin 2θ ∂_θ f - c₂(θ) D_z f`,
  `Vfs α   = (3/(2α)) sin 2θ ∂_θ F_* - c₂(θ) D_z F_*`.

The second summand `Mf f · Vfs α` is *separated*: `Vfs α` is the sum of two products of an
angular factor and a radial factor, and it is this separation which makes the estimate work
(the radial profile is only `O(z)` at the axis, so `Vfs` does **not** lie in `ℋ³`; it is the
product with the vanishing radial factor `L₁₂(f)` which lies in `ℋ³`).  This module fixes the
two angular factors and their `ℋ³`-majorant:

* `VfsRad z = 2z/(1+z)²` and `VfsRadZ z = (Zop VfsRad) z = z ∂_z VfsRad z` are the two radial
  factors;
* `VfsGc α θ = Γ(θ)/c(α)`;
* `VfsA1 α θ = (3/2)·(dthU (VfsGc α)) θ`;
* `VfsA2 α θ = -α·c₂(θ)·VfsGc α θ`;
* `angMaj α C` is the angular majorant

  `(C θ)² sin(2θ)^{-η} + Σ_{1 ≤ i ≤ 3} (dthU^i C θ)² sin(2θ)^{-γ(α)}`

  of a single angular profile — exactly the angular factor produced by
  `Work.FTS.StrongPersist.L3Aux.HkIntegrand_sep_le` at order three;
* `VfsAngMaj α = angMaj α (VfsA1 α) + angMaj α (VfsA2 α)`.

The separated identity `Vfs α z θ = VfsA1 α θ · VfsRad z + VfsA2 α θ · VfsRadZ z` and the
bound `∫_θ VfsAngMaj α ≤ K` (both `α`-uniform, `0 < α ≤ 1`) are the two facts proved about
this vocabulary.  Nothing here is a proof obligation.
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.StrongPersist.L3Rhs.N0gDecomp
import Submission.Work.Spaces.MixedMulDefs
import Submission.Work.Spaces.GammaW_Prelim
import Submission.Work.Construction.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.L3Rhs

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## The two radial factors -/

/-- The radial profile `z ↦ 2z/(1+z)²` of the star solution `F_*`. -/
def VfsRad (z : ℝ) : ℝ := 2 * z / (1 + z) ^ 2

/-- The second radial factor `z ↦ (Zop VfsRad) z = z ∂_z VfsRad z`. -/
def VfsRadZ (z : ℝ) : ℝ := Work.Spaces.Zop VfsRad z

/-! ## The two angular factors -/

/-- The angular profile `Γ(θ)/c(α)`. -/
def VfsGc (α : ℝ) (θ : ℝ) : ℝ := Work.Spaces.Gam α θ / Work.Spaces.c α

/-- The first angular factor of `Vfs`: `(3/2)·(dthU (Γ/c)) θ` (note `dthU ψ = sin 2θ · ψ'`
already carries the factor `sin 2θ` which comes from `pth F_* = sin 2θ · ∂_θ F_*`). -/
def VfsA1 (α : ℝ) (θ : ℝ) : ℝ :=
  (3 / 2) * Work.Spaces.dthU (VfsGc α) θ

/-- The second angular factor of `Vfs`: `-α·c₂(θ)·Γ(θ)/c(α)`. -/
def VfsA2 (α : ℝ) (θ : ℝ) : ℝ :=
  -α * Work.Construction.c2m θ * VfsGc α θ

/-! ## The angular majorants -/

/-- The angular majorant of a single angular profile `C` at order three: the angular factor
produced by `HkIntegrand_sep_le`. -/
def angMaj (α : ℝ) (C : ℝ → ℝ) (θ : ℝ) : ℝ :=
  (C θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
    + ∑ i ∈ Finset.range 4,
        (if 1 ≤ i then (Work.Spaces.dthU^[i] C θ) ^ 2
          * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) else 0)

/-- The angular majorant of the separated summand `Mf f · Vfs α`. -/
def VfsAngMaj (α : ℝ) (θ : ℝ) : ℝ := angMaj α (VfsA1 α) θ + angMaj α (VfsA2 α) θ

end Work.FTS.StrongPersist.L3Rhs
