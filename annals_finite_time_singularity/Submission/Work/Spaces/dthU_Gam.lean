import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.Spaces.GammaW_Prelim
import Submission.Work.Spaces.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
`D_θ Γ = α q Γ` on the open quadrant.

With `Γ(θ) = (sin θ · cos²θ)^{α/3}` and `D_θ = sin(2θ) ∂_θ`, the chain rule gives
`D_θ Γ = α q Γ` where `q(θ) = cos(2θ) - 1/3 = (2/3)(cos²θ - 2 sin²θ)`.
-/

open scoped Real

namespace Work.Spaces

theorem dthU_Gam (α θ : ℝ) (hα : 0 < α) (hθ : θ ∈ Set.Ioo 0 (π/2)) :
    Work.Spaces.dthU (fun t => Work.Spaces.Gam α t) θ
      = α * Work.Spaces.qfun θ * Work.Spaces.Gam α θ := by
  have hθ0 : 0 < θ := hθ.1
  have hθ1 : θ < Real.pi / 2 := hθ.2
  have hsin : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi hθ0 (by linarith [Real.pi_pos])
  have hcos : 0 < Real.cos θ := Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hθ1⟩
  have hG : 0 < Real.sin θ * Real.cos θ ^ 2 := by positivity
  -- the derivative of the inner function `θ ↦ sin θ · cos²θ`
  have hprod : HasDerivAt (fun t => Real.sin t * Real.cos t ^ 2)
      (Real.cos θ * Real.cos θ ^ 2
        + Real.sin θ * (2 * Real.cos θ ^ (2 - 1) * (-Real.sin θ))) θ :=
    (Real.hasDerivAt_sin θ).mul ((Real.hasDerivAt_cos θ).pow 2)
  have hrpow := hprod.rpow_const (p := α / 3) (Or.inl (ne_of_gt hG))
  have hderiv : deriv (fun t => Work.Spaces.Gam α t) θ
      = (Real.cos θ * Real.cos θ ^ 2
          + Real.sin θ * (2 * Real.cos θ ^ (2 - 1) * (-Real.sin θ))) * (α / 3)
        * (Real.sin θ * Real.cos θ ^ 2) ^ (α / 3 - 1) :=
    hrpow.deriv
  -- the angular identity `q(θ) = cos(2θ) - 1/3 = cos²θ - sin²θ - 1/3`
  have hcos2 : Real.cos (2 * θ) = Real.cos θ ^ 2 - Real.sin θ ^ 2 := by
    rw [Real.cos_two_mul]
    linarith [Real.sin_sq_add_cos_sq θ]
  -- the degree-two form of `q`
  have hq2 : (2 / 3 : ℝ) * (Real.cos θ ^ 2 - 2 * Real.sin θ ^ 2)
      = Real.cos θ ^ 2 - Real.sin θ ^ 2 - 1 / 3 := by
    nlinarith [Real.sin_sq_add_cos_sq θ]
  have hdG : Real.cos θ * Real.cos θ ^ 2
        + Real.sin θ * (2 * Real.cos θ ^ (2 - 1) * (-Real.sin θ))
      = Real.cos θ * (Real.cos θ ^ 2 - 2 * Real.sin θ ^ 2) := by
    norm_num
    ring
  -- the coefficient identity, with the `rpow` factor stripped off
  have hcoef : Real.sin (2 * θ) *
        ((Real.cos θ * Real.cos θ ^ 2
          + Real.sin θ * (2 * Real.cos θ ^ (2 - 1) * (-Real.sin θ))) * (α / 3))
      = α * Work.Spaces.qfun θ * (Real.sin θ * Real.cos θ ^ 2) := by
    rw [Work.Spaces.qfun_apply, Real.sin_two_mul, hcos2, hdG]
    linear_combination (Real.sin θ * Real.cos θ ^ 2 * α) * hq2
  -- `g^{α/3} = g^{α/3-1} · g`, which lets the `rpow` factor be pulled out
  have hrpowg : (Real.sin θ * Real.cos θ ^ 2) ^ (α / 3)
      = (Real.sin θ * Real.cos θ ^ 2) ^ (α / 3 - 1) * (Real.sin θ * Real.cos θ ^ 2) := by
    conv_lhs => rw [show α / 3 = (α / 3 - 1) + 1 from by ring]
    rw [Real.rpow_add hG (α / 3 - 1) 1, Real.rpow_one]
  rw [Work.Spaces.dthU_apply, hderiv]
  show Real.sin (2 * θ) *
        ((Real.cos θ * Real.cos θ ^ 2
            + Real.sin θ * (2 * Real.cos θ ^ (2 - 1) * (-Real.sin θ))) * (α / 3)
          * (Real.sin θ * Real.cos θ ^ 2) ^ (α / 3 - 1))
      = α * Work.Spaces.qfun θ * (Real.sin θ * Real.cos θ ^ 2) ^ (α / 3)
  rw [hrpowg]
  have e1 : Real.sin (2 * θ) *
        ((Real.cos θ * Real.cos θ ^ 2
            + Real.sin θ * (2 * Real.cos θ ^ (2 - 1) * (-Real.sin θ))) * (α / 3)
          * (Real.sin θ * Real.cos θ ^ 2) ^ (α / 3 - 1))
      = (Real.sin (2 * θ) * ((Real.cos θ * Real.cos θ ^ 2
            + Real.sin θ * (2 * Real.cos θ ^ (2 - 1) * (-Real.sin θ))) * (α / 3)))
        * (Real.sin θ * Real.cos θ ^ 2) ^ (α / 3 - 1) := by ring
  have e2 : α * Work.Spaces.qfun θ *
        ((Real.sin θ * Real.cos θ ^ 2) ^ (α / 3 - 1) * (Real.sin θ * Real.cos θ ^ 2))
      = (α * Work.Spaces.qfun θ * (Real.sin θ * Real.cos θ ^ 2))
        * (Real.sin θ * Real.cos θ ^ 2) ^ (α / 3 - 1) := by ring
  rw [e1, e2, hcoef]

end Work.Spaces
