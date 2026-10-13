/-
Interior regularity of `bslOp α`: the transported problem in the coordinates `(σ,θ)` of `ℝ × ℝ`.

The change of variables `z = exp (α σ)` (with Jacobian `α exp (α σ)`) turns the weak formulation
of `bslOp α Ψ = F` on the open quadrant `Q0 = (0,∞) × (0,π/2)`, tested against
`φ (z,θ) = ψ ((1/α) log z, θ)`, into the statement

  `∫_{ℝ×(0,π/2)} V · KopD ψ = ∫_{ℝ×(0,π/2)} G · ψ`,

where

* `V (σ,θ) = α exp (5σ) cos θ · Ψ (exp (ασ), θ)` (`VRR`), and `G` the analogue for `F`;
* `KopD ψ = -∂_σσψ - ∂_θθψ - 5 ∂_σψ + tan θ · ∂_θψ + (tan²θ - 5) ψ` (`kopD`),

i.e. the operator `bslOp` in the `(σ,θ)`-coordinates (`Work.EllipticEst.InteriorRegularity.
bslOp_comp_exp`).

This module fixes that vocabulary (the `ℝ×ℝ` counterpart of `Strip.Kop`/`Q0.Vf`); the transport
itself is `Q0.transportWeakRR`.
-/
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.EllipticEst.InteriorRegularity.Strip
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

namespace Work.EllipticEst.InteriorRegularity.Q0

set_option autoImplicit false
set_option linter.unusedVariables false

/-- The half-strip `ℝ × (0,π/2)` of the `(σ,θ)`-coordinates. -/
def stripRR : Set (ℝ × ℝ) := Set.univ ×ˢ Set.Ioo 0 (Real.pi / 2)

/-- The transported weight `α exp (5σ) cos θ`
(= the Jacobian `α exp (ασ)` times the weight `z^((5-α)/α) cos θ` at `z = exp (ασ)`). -/
def wtRR (α : ℝ) (σ θ : ℝ) : ℝ := α * Real.exp (5 * σ) * Real.cos θ

/-- The transported unknown, zero off the half-strip. -/
def VRR (α : ℝ) (Ψ : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ :=
  fun σ θ => if θ ∈ Set.Ioo 0 (Real.pi / 2) then wtRR α σ θ * Ψ (Real.exp (α * σ)) θ else 0

/-- The transported source, zero off the half-strip. -/
def GRR (α : ℝ) (F : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ :=
  fun σ θ => if θ ∈ Set.Ioo 0 (Real.pi / 2) then wtRR α σ θ * F (Real.exp (α * σ)) θ else 0

/-- The operator `bslOp` in the `(σ,θ)`-coordinates (the `deriv`-level version of `Strip.Kop`). -/
def kopD (ψ : ℝ → ℝ → ℂ) (σ θ : ℝ) : ℂ :=
  - deriv (fun σ' => deriv (fun σ'' => ψ σ'' θ) σ') σ
    - deriv (fun θ' => deriv (fun θ'' => ψ σ θ'') θ') θ
    - 5 * deriv (fun σ' => ψ σ' θ) σ
    + (Real.tan θ : ℂ) * deriv (fun θ' => ψ σ θ') θ
    + ((Real.tan θ) ^ 2 - 5 : ℝ) * ψ σ θ

theorem kopD_apply (ψ : ℝ → ℝ → ℂ) (σ θ : ℝ) :
    kopD ψ σ θ = - deriv (fun σ' => deriv (fun σ'' => ψ σ'' θ) σ') σ
      - deriv (fun θ' => deriv (fun θ'' => ψ σ θ'') θ') θ
      - 5 * deriv (fun σ' => ψ σ' θ) σ
      + (Real.tan θ : ℂ) * deriv (fun θ' => ψ σ θ') θ
      + ((Real.tan θ) ^ 2 - 5 : ℝ) * ψ σ θ := rfl

/-- The weak identity in the `(σ,θ)`-coordinates. -/
def StripWeakRR (U G : ℝ → ℝ → ℂ) : Prop :=
  ∀ ψ : ℝ → ℝ → ℂ, (∀ n : ℕ, ContDiff ℝ n (Function.uncurry ψ)) →
    HasCompactSupport (Function.uncurry ψ) → tsupport (Function.uncurry ψ) ⊆ stripRR →
    ∫ q : ℝ × ℝ, U q.1 q.2 * kopD ψ q.1 q.2 = ∫ q : ℝ × ℝ, G q.1 q.2 * ψ q.1 q.2

end Work.EllipticEst.InteriorRegularity.Q0
