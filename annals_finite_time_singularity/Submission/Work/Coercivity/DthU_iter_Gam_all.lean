import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.Spaces.Gamma_WlInf

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `D_θ^{j+1} Γ = α · Tfun j α · Γ` on `(0, π/2)`, for **every** real `α`

The paper's angular identity is normally stated for `α > 0` (see
`Work.Spaces.dthU_iter_Gam`).  Here we remove that hypothesis: the identity is a
purely algebraic/analytic statement in `α` and holds for arbitrary real `α`.

The only place the positivity of `α` was used in the `Spaces` development is the
base case `D_θ Γ = α q Γ`, and there it is in fact unnecessary: the underlying
derivative computation is valid for every `α` because `sin θ · cos²θ > 0` on
`(0, π/2)`.  We reprove that base case harmlessly as `dthU_Gam_all`, and then
repeat the induction over `j`.
-/

open scoped Real Topology
open Set Filter

namespace Work.Coercivity

/-- The base case `D_θ Γ = α · q · Γ`, valid for **arbitrary** real `α`
(the `Spaces` version `dthU_Gam` carries a redundant hypothesis `0 < α`). -/
theorem dthU_Gam_all (α θ : ℝ) (hθ : θ ∈ Set.Ioo 0 (π/2)) :
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

/-- The paper's identity `D_θ^{j+1} Γ = α · Tfun j α · Γ` on `(0, π/2)`,
for **every** real `α`. -/
theorem DthU_iter_Gam_all (j : ℕ) (α : ℝ) :
    Set.EqOn (Work.Spaces.dthU^[j+1] (fun t => Work.Spaces.Gam α t))
      (fun θ => α * Work.Spaces.Tfun j α θ * Work.Spaces.Gam α θ)
      (Set.Ioo 0 (π/2)) := by
  induction j with
  | zero =>
      intro θ hθ
      rw [Function.iterate_one]
      simpa only [Work.Spaces.Tfun_zero] using dthU_Gam_all α θ hθ
  | succ j ih =>
      intro θ hθ
      rw [Function.iterate_succ_apply']
      have hmem : Set.Ioo (0:ℝ) (π/2) ∈ 𝓝 θ := IsOpen.mem_nhds isOpen_Ioo hθ
      have hev := ih.eventuallyEq_of_mem hmem
      have hderiv := hev.deriv_eq
      have hstep : Work.Spaces.dthU
            (Work.Spaces.dthU^[j+1] (fun t => Work.Spaces.Gam α t)) θ
          = Work.Spaces.dthU
            (fun θ => α * Work.Spaces.Tfun j α θ * Work.Spaces.Gam α θ) θ := by
        rw [Work.Spaces.dthU_apply, Work.Spaces.dthU_apply, hderiv]
      rw [hstep]
      have hT : DifferentiableAt ℝ (fun θ => α * Work.Spaces.Tfun j α θ) θ :=
        ((Work.Spaces.Tfun_smooth j α).differentiable (by simp)).differentiableAt.const_mul α
      have hG : DifferentiableAt ℝ (fun t => Work.Spaces.Gam α t) θ :=
        Work.Spaces.Gam_differentiableAt α θ hθ.1 hθ.2
      have hcomp : (fun θ => α * Work.Spaces.Tfun j α θ * Work.Spaces.Gam α θ)
          = (fun θ => α * Work.Spaces.Tfun j α θ) * (fun t => Work.Spaces.Gam α t) := rfl
      rw [hcomp, Work.Spaces.dthU_mul_apply (fun θ => α * Work.Spaces.Tfun j α θ)
            (fun t => Work.Spaces.Gam α t) θ hT hG,
        Work.Spaces.dthU_const_mul_apply α (Work.Spaces.Tfun j α) θ,
        show Work.Spaces.dthU (fun t => Work.Spaces.Gam α t) θ
              = α * Work.Spaces.qfun θ * Work.Spaces.Gam α θ from dthU_Gam_all α θ hθ]
      simp only [Work.Spaces.Tfun_succ, Work.Spaces.dthU_apply]
      ring_nf

end Work.Coercivity
