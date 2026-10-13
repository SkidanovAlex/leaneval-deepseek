/-
Copyright: work module for the Elgindi finite-time singularity project.

# `ProfRHSAux/OpAdd` — linearity of `ℛ, U, V` in their argument

The operators `ℛ(Ψ) = (2 sinθ Ψ + α sinθ z ∂_zΨ + cosθ ∂_θΨ)/cosθ`, `U(Ψ) = -3Ψ - α z ∂_zΨ` and
`V(Ψ) = ∂_θΨ - tanθ·Ψ` of §Modulation are linear in `Ψ` on the open quadrant, where the slices
are differentiable.  The lemma `abs_deriv_add_le` records the totalised-`deriv` form of
`|∂(f+g)| ≤ |∂f| + |∂g|` which holds when only `f` is known to be differentiable.
-/
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.InnerProductSpace.Basic
import Submission.Work.Construction.Defs
import Submission.Work.FTS.Galerkin.Defs
import Submission.Work.Spaces.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.EpsRLX.ProfRHSAux

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-! ## A derivative bound for sums -/

/-- **`|∂(f + g)| ≤ |∂f| + |∂g|` when only `f` is known to be differentiable.**  If `g` is
differentiable too this is the triangle inequality applied to `deriv_add`; if it is not, then
`f + g` is not differentiable and Lean's totalised `deriv` returns `0`. -/
theorem abs_deriv_add_le {f g : ℝ → ℝ} {x : ℝ} (hf : DifferentiableAt ℝ f x) :
    |deriv (fun y => f y + g y) x| ≤ |deriv f x| + |deriv g x| := by
  by_cases hg : DifferentiableAt ℝ g x
  · rw [show deriv (fun y => f y + g y) x = deriv f x + deriv g x from deriv_add hf hg]
    exact abs_add_le _ _
  · have hfg : ¬ DifferentiableAt ℝ (fun y => f y + g y) x := by
      intro h
      refine hg ?_
      have h2 : DifferentiableAt ℝ (fun y => (f y + g y) - f y) x := h.sub hf
      have h3 : (fun y => (f y + g y) - f y) = g := by funext y; ring
      rwa [h3] at h2
    rw [deriv_zero_of_not_differentiableAt hfg, abs_zero]
    exact add_nonneg (abs_nonneg _) (abs_nonneg _)

/-! ## Linearity of `ℛ, U, V` in their argument -/

/-- **`ℛ` is additive in its argument** (on the open quadrant, where the slices are
differentiable). -/
theorem Rop_add {α : ℝ} {A B : ℝ → ℝ → ℝ} {z θ : ℝ}
    (hA1 : DifferentiableAt ℝ (fun z' => A z' θ) z)
    (hB1 : DifferentiableAt ℝ (fun z' => B z' θ) z)
    (hA2 : DifferentiableAt ℝ (fun θ' => A z θ') θ)
    (hB2 : DifferentiableAt ℝ (fun θ' => B z θ') θ) :
    Work.Construction.Rop α (fun z θ => A z θ + B z θ) z θ
      = Work.Construction.Rop α A z θ + Work.Construction.Rop α B z θ := by
  have hz' : Work.Spaces.pz (fun z θ => A z θ + B z θ) z θ
      = Work.Spaces.pz A z θ + Work.Spaces.pz B z θ := by
    simp only [Work.Spaces.pz]
    rw [show (fun z' => (fun z θ => A z θ + B z θ) z' θ)
          = (fun z' => A z' θ) + (fun z' => B z' θ) from rfl, deriv_add hA1 hB1]
  have ht' : Work.Spaces.pth (fun z θ => A z θ + B z θ) z θ
      = Work.Spaces.pth A z θ + Work.Spaces.pth B z θ := by
    simp only [Work.Spaces.pth]
    rw [show (fun θ' => (fun z θ => A z θ + B z θ) z θ')
          = (fun θ' => A z θ') + (fun θ' => B z θ') from rfl, deriv_add hA2 hB2]
  simp only [Work.Construction.Rop, hz', ht']
  ring

/-- **`U` is additive in its argument.** -/
theorem Uop_add {α : ℝ} {A B : ℝ → ℝ → ℝ} {z θ : ℝ}
    (hA1 : DifferentiableAt ℝ (fun z' => A z' θ) z)
    (hB1 : DifferentiableAt ℝ (fun z' => B z' θ) z) :
    Work.Construction.Uop α (fun z θ => A z θ + B z θ) z θ
      = Work.Construction.Uop α A z θ + Work.Construction.Uop α B z θ := by
  have hz' : Work.Spaces.pz (fun z θ => A z θ + B z θ) z θ
      = Work.Spaces.pz A z θ + Work.Spaces.pz B z θ := by
    simp only [Work.Spaces.pz]
    rw [show (fun z' => (fun z θ => A z θ + B z θ) z' θ)
          = (fun z' => A z' θ) + (fun z' => B z' θ) from rfl, deriv_add hA1 hB1]
  simp only [Work.Construction.Uop, hz']
  ring

/-- **`V` is additive in its argument.** -/
theorem Vop_add {A B : ℝ → ℝ → ℝ} {z θ : ℝ}
    (hA2 : DifferentiableAt ℝ (fun θ' => A z θ') θ)
    (hB2 : DifferentiableAt ℝ (fun θ' => B z θ') θ) :
    Work.Construction.Vop (fun z θ => A z θ + B z θ) z θ
      = Work.Construction.Vop A z θ + Work.Construction.Vop B z θ := by
  have ht' : Work.Spaces.pth (fun z θ => A z θ + B z θ) z θ
      = Work.Spaces.pth A z θ + Work.Spaces.pth B z θ := by
    simp only [Work.Spaces.pth]
    rw [show (fun θ' => (fun z θ => A z θ + B z θ) z θ')
          = (fun θ' => A z θ') + (fun θ' => B z θ') from rfl, deriv_add hA2 hB2]
  simp only [Work.Construction.Vop, ht']
  ring

end Work.FTS.StrongEps.EpsRLX.ProfRHSAux
