import Mathlib
import Submission.Work.RPA3.Defs
import Submission.Work.RPA3.Symp
import Submission.Work.RPA3.contDiff_param_intervalIntegral

/-!
# RPA3, D1: the flux primitive (definitions)

The flux form of a family `(τ,x,t) ↦ ℓ τ x t` of Lagrangians is `β = ω(∂_τℓ, ·)`.  Its two
components along the family are

`bxf L τ x t = ω(∂_τℓ(τ,x,t), ∂_xℓ(τ,x,t))`,  `btf L τ x t = ω(∂_τℓ(τ,x,t), ∂_tℓ(τ,x,t))`,

and the primitive is

`Hf L τ x t = -∫_{u=-X₀}^{x} β_u(τ,u,t) du`,

written as a *fixed interval* integral `-((x+X₀) * ∫_{σ∈[0,1]} bxf L τ (-X₀ + σ*(x+X₀)) t dσ)`
so that smoothness in `(τ,x,t)` is `contDiff_param_intervalIntegral`.

This module only fixes the notation; the lemmas about it live in the sibling modules under
`Submission/Work/RPA3/FluxPrim/`.
-/

open scoped ContDiff
open scoped Interval

set_option autoImplicit false

noncomputable section

namespace Work.RPA3

/-- The linear part `S` of `τ_π` (`τ_π` itself is the affine map `S + ((0,π),(0,0))`).  It is a
symplectic linear map: `Work.RPA3.symp_tauLin`. -/
def tauLin (a : PS) : PS := ((-a.1.1, a.1.2), (-a.2.1, a.2.2))

@[simp] theorem symp_tauLin (a b : PS) : symp (tauLin a) (tauLin b) = symp a b := by
  simp only [symp, tauLin]; ring

theorem symp_tauLin_right (a b : PS) : symp a (tauLin b) = symp (tauLin a) b := by
  simp only [symp, tauLin]; ring

/-- The `x`-component of the flux form `β = ω(∂_τℓ, ·)`. -/
def bxf (L : LagFamily) (τ x t : ℝ) : ℝ :=
  symp (deriv (fun σ => L.ℓ σ (x, t)) τ) (deriv (fun y => L.ℓ τ (y, t)) x)

/-- The `t`-component of the flux form `β = ω(∂_τℓ, ·)`. -/
def btf (L : LagFamily) (τ x t : ℝ) : ℝ :=
  symp (deriv (fun σ => L.ℓ σ (x, t)) τ) (deriv (fun s => L.ℓ τ (x, s)) t)

/-- The integrand of the fixed-interval form of the primitive:
`(x+X₀) * β_u(τ, -X₀ + σ(x+X₀), t)`, with `w = ((τ,(x,t)),σ)`. -/
def HfIntegrand (L : LagFamily) (w : (ℝ × (ℝ × ℝ)) × ℝ) : ℝ :=
  (w.1.2.1 + L.X0) * bxf L w.1.1 (-(L.X0) + (w.1.2.1 + L.X0) * w.2) w.1.2.2

/-- The flux primitive, evaluated: `-∫_{u=-X₀}^{x} β_u du`, as a fixed-interval parametric
integral over `σ ∈ [0,1]` of `(x+X₀) * β_u(τ, -X₀ + σ(x+X₀), t)`. -/
def Hf (L : LagFamily) (τ x t : ℝ) : ℝ :=
  -(∫ σ in (0 : ℝ)..1, HfIntegrand L ((τ, (x, t)), σ))

/-- The flux primitive as a function `ℝ → ℝ × ℝ → ℝ` of `(τ, (x,t))`. -/
def hf (L : LagFamily) : ℝ → ℝ × ℝ → ℝ := fun τ p => Hf L τ p.1 p.2

end Work.RPA3
