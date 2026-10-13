/-
# Auxiliary definitions for the `D_θ`-coercivity estimate (`thetaDerivative`)

The paper's Proposition `prop:thetaderivative` (Elgindi, Annals 194 (3) 2021,
§"Linearization with angular transport") states, with `D_θ = sin(2θ) ∂_θ`,

  `(D_θ 𝓛_Γ^T f, D_θ f · w²/sin(2θ)^γ)_{L²} ≥ (1/4 - α)|D_θ f · w/√sin(2θ)^γ|² - 10⁷ α|f w|²`.

Its proof expands `D_θ(𝓛_Γ^T f)` pointwise.  Since `D_θ` commutes with `𝓛` and kills
radial functions, and since `𝓛_Γ^T = 𝓛_Γ - 𝕡(Transport)` with
`𝓛_Γ = 𝓛 - (2zΓ/(c(1+z)²))L₁₂` and `𝕡(g) = g - (Γ/c)(2z²/(1+z)³)L₁₂(g)(0)`, one gets

  `D_θ 𝓛_Γ^T f = [𝓛(D_θ f) - (3/(1+z)) D_θ(D_θ f)]
                    - D_θΓ · (2z/(c(1+z)²)) L₁₂(f)
                    + (D_θΓ/c) · (2z²/(1+z)³) L₁₂(Transport f)(0)`,

i.e. `Aop (D_θ f) + T2 + T4` in the notation below.  This file fixes the names of
these objects so that the main file and the delegated lemmas can share them.
-/
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.Coercivity.Defs
import Submission.Work.Coercivity.Basic
import Submission.Work.Coercivity.zAux

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.Coercivity

set_option autoImplicit false

/-- The angular weight `ρ = w(z)²·sin(2θ)^{-γ}`, `γ = gam α`, appearing in the target
`thetaDerivative` (it is the weight against which `D_θ f` is squared in `EDth`). -/
def thetaW (α : ℝ) (z θ : ℝ) : ℝ :=
  Spaces.w z ^ 2 * (Real.sin (2 * θ)) ^ (-(Spaces.gam α))

/-- `D_θΓ = sin(2θ) ∂_θΓ`, shown as a function of `z` (it does not depend on `z`). -/
def DthGam (α : ℝ) (z θ : ℝ) : ℝ :=
  Spaces.Dth (fun _ θ' => Spaces.Gam α θ') z θ

/-- The operator `𝓛 - (3/(1+z)) D_θ`; on `D_θ f` it is the coercive part of
`D_θ(𝓛_Γ^T f)` (the `𝓛(D_θ f)` term together with the angular-transport term, whose
`θ`-integration by parts is favourable). -/
def Aop (f : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ :=
  fun z θ => L f z θ - (3 / (1 + z)) * Spaces.Dth f z θ

/-- The first `D_θΓ`-term of `D_θ(𝓛_Γ^T f)`:
`-D_θΓ · (2z/(c(1+z)²)) · L₁₂(f)`. -/
def T2 (α : ℝ) (f : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ :=
  fun z θ => -(DthGam α z θ) * (2 * z / (Spaces.c α * (1 + z) ^ 2)) * L12f f z

/-- The projector `D_θΓ`-term of `D_θ(𝓛_Γ^T f)`:
`(D_θΓ/c) · (2z²/(1+z)³) · L₁₂(Transport f)(0)`. -/
def T4 (α : ℝ) (f : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ :=
  fun z θ => (DthGam α z θ / Spaces.c α) * (2 * z ^ 2 / (1 + z) ^ 3) * C0 f

theorem thetaW_eq (α z θ : ℝ) :
    thetaW α z θ = Spaces.w z ^ 2 * (Real.sin (2 * θ)) ^ (-(Spaces.gam α)) := rfl

theorem Aop_eq (f : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Aop f z θ = L f z θ - (3 / (1 + z)) * Spaces.Dth f z θ := rfl

theorem DthGam_eq (α z θ : ℝ) :
    DthGam α z θ = Real.sin (2 * θ) * deriv (fun θ' => Spaces.Gam α θ') θ := rfl

end Work.Coercivity
