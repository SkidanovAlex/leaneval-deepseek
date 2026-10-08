import Mathlib
import Submission.Work.Induction.Defs

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.Induction

open Classical
open scoped Pointwise

-- Projection formula: pointwise every summand of `Ind_H^G (φ * Res ψ)` at `g` is
-- `φ (x*g*x⁻¹) * ψ (x*g*x⁻¹)`, and `x*g*x⁻¹` is conjugate to `g`, so `ψ` a class function
-- gives `ψ (x*g*x⁻¹) = ψ g`; factor `ψ g` out of the defining sum.
theorem indFun_mul_res {G : Type*} [Group G] [Fintype G] (H : Subgroup G) (φ : H → ℂ)
    (ψ : G → ℂ) (hψ : Work.CharCore.IsClassFun ψ) :
    Work.Induction.indFun H (φ * Work.Induction.resFun H ψ)
      = Work.Induction.indFun H φ * ψ := by
  ext g
  rw [Pi.mul_apply, Work.Induction.indFun_apply_def, Work.Induction.indFun_apply_def]
  -- Every summand of the induced function at `g` splits off the factor `ψ g`.
  have key : ∀ x : G, (if hx : x * g * x⁻¹ ∈ H then (φ * Work.Induction.resFun H ψ) ⟨x * g * x⁻¹, hx⟩ else 0)
      = (if hx : x * g * x⁻¹ ∈ H then φ ⟨x * g * x⁻¹, hx⟩ else 0) * ψ g := by
    intro x
    by_cases hx : x * g * x⁻¹ ∈ H
    · rw [dite_eq_left hx, dite_eq_left hx, Pi.mul_apply, Work.Induction.resFun_apply, hψ g x]
    · rw [dite_eq_right hx, dite_eq_right hx, zero_mul]
  rw [show (∑ x : G, (if hx : x * g * x⁻¹ ∈ H then (φ * Work.Induction.resFun H ψ) ⟨x * g * x⁻¹, hx⟩ else 0))
        = ∑ x : G, (if hx : x * g * x⁻¹ ∈ H then φ ⟨x * g * x⁻¹, hx⟩ else 0) * ψ g
      from Finset.sum_congr rfl fun x _ => key x]
  rw [← Finset.sum_mul]
  ring

end Work.Induction
