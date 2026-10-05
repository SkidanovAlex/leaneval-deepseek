import Mathlib
import Submission.Work.RPA3.follow_family_defs

namespace Work.RPA3

set_option autoImplicit false

noncomputable section

/-! # The Fréchet derivative of `Efun L`

`Efun L = fun z : ℝ × (ℝ × ℝ) => L.ℓ z.1 z.2` is the uncurried family map.  Its Fréchet
derivative at `(τ, (x,t))` applied to a direction `(a, (b, c))` is
`a • ∂_τℓ + b • ∂_xℓ + c • ∂_tℓ`; this file records the special case `a = 1` needed by the
route, in the exact form `dTau + y₁ • dX + y₂ • dT` in which it is used.

The proof is the standard one: `Efun L` is `C⁸` (its smoothness is the field
`LagFamilyAll.smooth` verbatim), so the Fréchet derivative applied to a vector `v` equals the
derivative at `0` of the line `s ↦ Efun L (p + s • v)`; reading off the three coordinate
directions `(1,(0,0))`, `(0,(1,0))`, `(0,(0,1))` gives `dTau`, `dX`, `dT` by the shift rule
for `deriv`, and linearity assembles the general direction. -/

/-- The shift rule for `deriv`: differentiating `s ↦ f (c + s)` at `0` is differentiating `f`
at `c`. -/
private theorem deriv_comp_add_const_zero {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : ℝ → E) (c : ℝ) : deriv (fun s : ℝ => f (c + s)) 0 = deriv f c := by
  rw [show (fun s : ℝ => f (c + s)) = fun s : ℝ => f (s + c) from by funext s; rw [add_comm]]
  rw [deriv_comp_add_const]
  simp

/-- The Fréchet derivative applied to a vector `v` is the derivative at `0` of the line
`s ↦ f (x + s • v)`. -/
private theorem fderiv_apply_eq_deriv_line {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {f : E → F} {x v : E}
    (hd : DifferentiableAt ℝ f x) :
    fderiv ℝ f x v = deriv (fun t : ℝ => f (x + t • v)) 0 := by
  rw [← DifferentiableAt.lineDeriv_eq_fderiv hd]
  rfl

theorem fderiv_Efun_apply (L : LagFamilyAll) (τ x t y₁ y₂ : ℝ) :
    fderiv ℝ (Efun L) (τ, (x, t)) ((1 : ℝ), (y₁, y₂))
      = dTau L τ x t + y₁ • dX L τ x t + y₂ • dT L τ x t := by
  have hd : DifferentiableAt ℝ (Efun L) (τ, (x, t)) :=
    (L.smooth.differentiable (by norm_num)).differentiableAt
  -- The three coordinate directions.
  have hA : fderiv ℝ (Efun L) (τ, (x, t)) ((1 : ℝ), ((0 : ℝ), (0 : ℝ))) = dTau L τ x t := by
    rw [fderiv_apply_eq_deriv_line hd]
    have hfun : (fun s : ℝ => Efun L ((τ, (x, t)) + s • ((1 : ℝ), ((0 : ℝ), (0 : ℝ)))))
        = fun s : ℝ => L.ℓ (τ + s) (x, t) := by
      funext s
      have : ((τ, (x, t)) + s • ((1 : ℝ), ((0 : ℝ), (0 : ℝ)))) = (τ + s, (x, t)) := by simp
      rw [this, Efun_apply]
    rw [hfun]
    simpa [dTau] using deriv_comp_add_const_zero (fun σ => L.ℓ σ (x, t)) τ
  have hB : fderiv ℝ (Efun L) (τ, (x, t)) ((0 : ℝ), ((1 : ℝ), (0 : ℝ))) = dX L τ x t := by
    rw [fderiv_apply_eq_deriv_line hd]
    have hfun : (fun s : ℝ => Efun L ((τ, (x, t)) + s • ((0 : ℝ), ((1 : ℝ), (0 : ℝ)))))
        = fun s : ℝ => L.ℓ τ (x + s, t) := by
      funext s
      have : ((τ, (x, t)) + s • ((0 : ℝ), ((1 : ℝ), (0 : ℝ)))) = (τ, (x + s, t)) := by simp
      rw [this, Efun_apply]
    rw [hfun]
    simpa [dX] using deriv_comp_add_const_zero (fun σ => L.ℓ τ (σ, t)) x
  have hC : fderiv ℝ (Efun L) (τ, (x, t)) ((0 : ℝ), ((0 : ℝ), (1 : ℝ))) = dT L τ x t := by
    rw [fderiv_apply_eq_deriv_line hd]
    have hfun : (fun s : ℝ => Efun L ((τ, (x, t)) + s • ((0 : ℝ), ((0 : ℝ), (1 : ℝ)))))
        = fun s : ℝ => L.ℓ τ (x, t + s) := by
      funext s
      have : ((τ, (x, t)) + s • ((0 : ℝ), ((0 : ℝ), (1 : ℝ)))) = (τ, (x, t + s)) := by simp
      rw [this, Efun_apply]
    rw [hfun]
    simpa [dT] using deriv_comp_add_const_zero (fun σ => L.ℓ τ (x, σ)) t
  -- Decompose the general direction into the three coordinate directions.
  have hdecomp : ((1 : ℝ), (y₁, y₂))
      = ((1 : ℝ), ((0 : ℝ), (0 : ℝ))) + y₁ • ((0 : ℝ), ((1 : ℝ), (0 : ℝ)))
        + y₂ • ((0 : ℝ), ((0 : ℝ), (1 : ℝ))) := by
    ext <;> simp
  rw [hdecomp]
  simp only [map_add, map_smul, hA, hB, hC]

end

end Work.RPA3
