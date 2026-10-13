import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Submission.Work.Cyl.Coords
import Submission.Work.Cyl.Frame
import Submission.Work.Cyl.Basic
import Submission.Work.Cyl.FieldDeriv

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The radial chain rule `r ↦ ρ ^ α`

If `F` is differentiable at `(ρ ^ α, θ)`, then differentiating `ρ' ↦ F (ρ' ^ α) θ` and using
`(ρ ^ α)' = α ρ ^ (α - 1)` gives `α ρ ^ α ∂_r F (ρ ^ α, θ) = ρ ∂_r (F (· ^ α, θ)) (ρ, θ)`.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace Work.Cyl

theorem alpha_mul_pow_mul_pdR (F : ℝ → ℝ → ℝ) (α ρ θ : ℝ) (hρ : 0 < ρ)
    (hF : Work.Cyl.DiffAt2 F (ρ ^ α) θ) :
    α * ρ ^ α * Work.Cyl.pdR F (ρ ^ α) θ = ρ * Work.Cyl.pdR (fun ρ' θ' => F (ρ' ^ α) θ') ρ θ := by
  have hρne : ρ ≠ 0 := ne_of_gt hρ
  have hg : DifferentiableAt ℝ (fun u : ℝ => F u θ) (ρ ^ α) :=
    differentiableAt_slice_fst F (ρ ^ α) θ hF
  have hf : DifferentiableAt ℝ (fun ρ' : ℝ => ρ' ^ α) ρ :=
    Real.differentiableAt_rpow_const_of_ne α hρne
  have hcomp : deriv (fun ρ' : ℝ => F (ρ' ^ α) θ) ρ =
      deriv (fun r' => F r' θ) (ρ ^ α) * (α * ρ ^ (α - 1)) := by
    rw [show (fun ρ' : ℝ => F (ρ' ^ α) θ) =
      ((fun u : ℝ => F u θ) ∘ (fun ρ' : ℝ => ρ' ^ α)) from rfl]
    rw [deriv_comp ρ hg hf, Real.deriv_rpow_const]
  rw [Work.Cyl.pdR, Work.Cyl.pdR, hcomp]
  have hpow : ρ ^ α = ρ ^ (α - 1) * ρ := by
    have h := Real.rpow_add hρ (α - 1) 1
    rw [Real.rpow_one, sub_add_cancel] at h
    exact h
  rw [hpow]
  ring

end Work.Cyl
