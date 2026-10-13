import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Complex.Trigonometric
import Submission.Work.Spaces.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
Auxiliary definitions for the proof that `Γ(θ)·z/(1+z)²` belongs to `𝒲^{l,∞}`
uniformly in `α ∈ (0,1]` (the paper's Proposition "ΓRegularity").
-/

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.Spaces

set_option autoImplicit false

/-- The angular coefficient `q(θ) = cos(2θ) - 1/3 = (2/3)·(cos²θ - 2 sin²θ)`.
It is the logarithmic angular derivative of `Γ`: on `(0, π/2)`,
`D_θ Γ = α · q · Γ`. -/
noncomputable def qfun (θ : ℝ) : ℝ := Real.cos (2 * θ) - 1/3

/-- Univariate version of `D_θ`: `dthU φ = sin(2θ) · φ'`. -/
noncomputable def dthU (φ : ℝ → ℝ) : ℝ → ℝ := fun θ => Real.sin (2 * θ) * deriv φ θ

/-- The coefficient sequence with `D_θ^{j+1} Γ = α · Tfun j α · Γ` (on `(0,π/2)`),
defined by `Tfun 0 = q` and `Tfun (j+1) = D_θ (Tfun j) + α · q · Tfun j`. -/
noncomputable def Tfun : ℕ → ℝ → ℝ → ℝ
  | 0, _α, θ => qfun θ
  | (j + 1), α, θ => Real.sin (2 * θ) * deriv (fun t => Tfun j α t) θ
      + α * qfun θ * Tfun j α θ

/-- The radial factor `z ↦ z/(1+z)²`. -/
noncomputable def hKer (z : ℝ) : ℝ := z / (1 + z) ^ 2

@[simp] theorem qfun_apply (θ : ℝ) : qfun θ = Real.cos (2 * θ) - 1/3 := rfl
@[simp] theorem dthU_apply (φ : ℝ → ℝ) (θ : ℝ) : dthU φ θ = Real.sin (2 * θ) * deriv φ θ := rfl
@[simp] theorem Tfun_zero (α θ : ℝ) : Tfun 0 α θ = qfun θ := rfl
theorem Tfun_succ (j : ℕ) (α θ : ℝ) :
    Tfun (j + 1) α θ = Real.sin (2 * θ) * deriv (fun t => Tfun j α t) θ
      + α * qfun θ * Tfun j α θ := rfl
@[simp] theorem hKer_apply (z : ℝ) : hKer z = z / (1 + z) ^ 2 := rfl

end Work.Spaces
