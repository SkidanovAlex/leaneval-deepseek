import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.InnerProductSpace.Basic
import Submission.Work.Construction.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EpsEngine

/-- Additivity of the three numerical operators of `Work.Construction` in their argument, at a
point where both summands are differentiable in `z` (for the `z ∂_z` in `Uop` and `Rop`) and in `θ`
(for the `∂_θ` in `Vop` and `Rop`).  This is the algebraic input of the block decomposition
`PhiTil α f (Φs + E f) = PhiTil α f (E f) + PhiTil α F_* Φs + Theta α F_*`: it turns the *sum* of
three profiles into the sum of the three operators, whose pieces are then bounded separately. -/
theorem Rop_Uop_Vop_add {α : ℝ} {Ψ₁ Ψ₂ : ℝ → ℝ → ℝ} {z θ : ℝ}
    (hz₁ : DifferentiableAt ℝ (fun z' => Ψ₁ z' θ) z)
    (hz₂ : DifferentiableAt ℝ (fun z' => Ψ₂ z' θ) z)
    (hθ₁ : DifferentiableAt ℝ (fun θ' => Ψ₁ z θ') θ)
    (hθ₂ : DifferentiableAt ℝ (fun θ' => Ψ₂ z θ') θ) :
    (Work.Construction.Rop α (fun z θ => Ψ₁ z θ + Ψ₂ z θ) z θ
        = Work.Construction.Rop α Ψ₁ z θ + Work.Construction.Rop α Ψ₂ z θ) ∧
    (Work.Construction.Uop α (fun z θ => Ψ₁ z θ + Ψ₂ z θ) z θ
        = Work.Construction.Uop α Ψ₁ z θ + Work.Construction.Uop α Ψ₂ z θ) ∧
    (Work.Construction.Vop (fun z θ => Ψ₁ z θ + Ψ₂ z θ) z θ
        = Work.Construction.Vop Ψ₁ z θ + Work.Construction.Vop Ψ₂ z θ) := by
  -- `pz` and `pth` are plain `deriv`s of the `z`- resp. `θ`-slices, so they are additive
  -- under the pointwise differentiability hypotheses; the three operator identities are
  -- then linear algebra in the ring `ℝ`.
  have hpz : Work.Spaces.pz (fun z θ => Ψ₁ z θ + Ψ₂ z θ) z θ
      = Work.Spaces.pz Ψ₁ z θ + Work.Spaces.pz Ψ₂ z θ := by
    simp only [Work.Spaces.pz]
    exact deriv_add hz₁ hz₂
  have hpt : Work.Spaces.pth (fun z θ => Ψ₁ z θ + Ψ₂ z θ) z θ
      = Work.Spaces.pth Ψ₁ z θ + Work.Spaces.pth Ψ₂ z θ := by
    simp only [Work.Spaces.pth]
    exact deriv_add hθ₁ hθ₂
  refine ⟨?_, ?_, ?_⟩ <;>
    simp only [Work.Construction.Rop, Work.Construction.Uop, Work.Construction.Vop,
      hpz, hpt] <;>
    ring

end Work.FTS.EpsEngine
