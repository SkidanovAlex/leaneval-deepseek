/-
Copyright: work module for the Elgindi finite-time singularity project.

# The divergence form of the `bslOp`-pairing

The pairing of `Work.Elliptic.bslOp α` against a test function `φ` with the weight
`z^{(5-α)/α} cos θ` on the open quadrant `Q0 = (0,∞) × (0,π/2)` is self-adjoint.  The point of
the weight is that it puts the second-order operator into divergence form:

* radial part: `z^β(-α²z²∂_zz - α(5+α)z∂_z) = -∂_z(α² z^{β+2} ∂_z)`  where `β = (5-α)/α`
  (the two exponents match exactly: `α²(β+2) = α(5+α)` when `αβ = 5-α`);
* angular part: `cos θ·L₀ = -∂_θ(cos θ·∂_θ) + (1/cos θ - 6cos θ)`.

Consequently, for `Φ, φ` smooth on the quadrant,

  `z^β cos θ·(L Φ·φ - Φ·L φ) = ∂_z(pairRad α Φ φ) + ∂_θ(pairAng α Φ φ)`,

which is the identity `pair_div_identity` of this directory; this module only fixes the
vocabulary (`pairBeta`, `pairWeight`, `pairRad`, `pairAng`) used by that identity and by the
assembly `Work.EllipticEst.Assembly.bslOp_pairing_self`.
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.Elliptic.Defs
import Submission.Work.FTS.EllipticEst.OpenQDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.EllipticEst.Assembly

set_option autoImplicit false

/-- The exponent `β = (5-α)/α` of the pairing weight.  With this exponent the radial part of
`bslOp` is in divergence form: `z^β(-α²z²∂_zz - α(5+α)z∂_z) = -∂_z(α²z^{β+2}∂_z)`, because
`α²(β+2) = α(5+α)`. -/
def pairBeta (α : ℝ) : ℝ := (5 - α) / α

/-- The pairing weight `z^{(5-α)/α}·cos θ` on which `bslOp α` is self-adjoint. -/
def pairWeight (α : ℝ) : ℝ × ℝ → ℝ := fun x => x.1 ^ pairBeta α * Real.cos x.2

/-- The radial component of the divergence form of `bslOp α`:
`A = α²z^{β+2}cos θ·(∂_zφ·Φ - ∂_zΦ·φ)`. -/
def pairRad (α : ℝ) (Φ φ : ℝ → ℝ → ℝ) : ℝ × ℝ → ℝ := fun x =>
  α ^ 2 * x.1 ^ (pairBeta α + 2) * Real.cos x.2
    * (Work.Spaces.pz φ x.1 x.2 * Φ x.1 x.2 - Work.Spaces.pz Φ x.1 x.2 * φ x.1 x.2)

/-- The angular component of the divergence form of `bslOp α`:
`B = z^β cos θ·(∂_θφ·Φ - ∂_θΦ·φ)`. -/
def pairAng (α : ℝ) (Φ φ : ℝ → ℝ → ℝ) : ℝ × ℝ → ℝ := fun x =>
  x.1 ^ pairBeta α * Real.cos x.2
    * (Work.Spaces.pth φ x.1 x.2 * Φ x.1 x.2 - Work.Spaces.pth Φ x.1 x.2 * φ x.1 x.2)

@[simp] theorem pairBeta_def (α : ℝ) : pairBeta α = (5 - α) / α := rfl

@[simp] theorem pairWeight_apply (α : ℝ) (x : ℝ × ℝ) :
    pairWeight α x = x.1 ^ pairBeta α * Real.cos x.2 := rfl

@[simp] theorem pairRad_apply (α : ℝ) (Φ φ : ℝ → ℝ → ℝ) (x : ℝ × ℝ) :
    pairRad α Φ φ x = α ^ 2 * x.1 ^ (pairBeta α + 2) * Real.cos x.2
      * (Work.Spaces.pz φ x.1 x.2 * Φ x.1 x.2 - Work.Spaces.pz Φ x.1 x.2 * φ x.1 x.2) :=
  rfl

@[simp] theorem pairAng_apply (α : ℝ) (Φ φ : ℝ → ℝ → ℝ) (x : ℝ × ℝ) :
    pairAng α Φ φ x = x.1 ^ pairBeta α * Real.cos x.2
      * (Work.Spaces.pth φ x.1 x.2 * Φ x.1 x.2 - Work.Spaces.pth Φ x.1 x.2 * φ x.1 x.2) :=
  rfl

/-- The exact matching of exponents behind the divergence form:
`α²(β+2) = α(5+α)` for `β = (5-α)/α`. -/
theorem sq_mul_pairBeta_add_two {α : ℝ} (hα : α ≠ 0) :
    α ^ 2 * (pairBeta α + 2) = α * (5 + α) := by
  rw [pairBeta_def]
  field_simp
  ring

end Work.EllipticEst.Assembly
