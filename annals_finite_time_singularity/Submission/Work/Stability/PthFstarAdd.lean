import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Submission.Work.Stability.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real Topology

namespace Work.Stability

/-- The `θ`-slice of the reference profile `F_* = α(Γ/c)·F_{*,rad}` is differentiable at every
`θ` in the open quadrant `(0, π/2)`: there `sin θ · cos²θ > 0`, so the angular profile
`Γ(θ) = (sin θ · cos²θ)^{α/3}` is differentiable by the chain rule for real powers, and the
remaining factor `α/F_{*,rad}`-combination is a constant of the slice. -/
theorem differentiableAt_Fstar_slice_theta (α z θ : ℝ) (hθ : 0 < θ ∧ θ < π / 2) :
    DifferentiableAt ℝ (fun θ' => Work.Construction.Fstar α z θ') θ := by
  have hsin : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi hθ.1 (by linarith [Real.pi_pos])
  have hcos : 0 < Real.cos θ := Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hθ.2⟩
  have hbase : Real.sin θ * Real.cos θ ^ 2 ≠ 0 := by positivity
  have hGam : DifferentiableAt ℝ (fun θ' => Work.Spaces.Gam α θ') θ := by
    rw [show Work.Spaces.Gam α = fun y : ℝ => (Real.sin y * Real.cos y ^ 2) ^ (α / 3) from rfl]
    exact (by fun_prop : DifferentiableAt ℝ (fun y : ℝ => Real.sin y * Real.cos y ^ 2) θ).rpow_const
      (Or.inl hbase)
  have h := ((hGam.div_const (Work.Spaces.c α)).const_mul α).mul_const (Work.FM.Fstar z)
  simpa [Work.Construction.Fstar] using h

/-- The `θ`-derivative of the full profile `F = F_* + g` splits:
`∂_θ(F_* + g) = ∂_θF_* + ∂_θg` whenever the slice of `g` is differentiable in `θ` at `θ`.
(`0 < θ < π/2` is exactly the differentiability range of the angular profile
`(sinθ cos²θ)^{α/3}`; on the open quadrant `Qd` it holds automatically.)  This discharges the
`hpth`-field of `Work.Stability.GDerivData`. -/
theorem PthFstarAdd {α : ℝ} {g : F3} {z θ s : ℝ} (hθ : 0 < θ ∧ θ < π / 2)
    (hg : DifferentiableAt ℝ (fun θ' => g z θ' s) θ) :
    Work.Spaces.pth (fun z' θ' => Ftot α g s z' θ') z θ
      = Work.Spaces.pth (Work.Construction.Fstar α) z θ + Work.Spaces.pth (slice g s) z θ := by
  have hF : DifferentiableAt ℝ (fun θ' => Work.Construction.Fstar α z θ') θ :=
    differentiableAt_Fstar_slice_theta α z θ hθ
  have hsum : (fun θ' => Work.Construction.Fstar α z θ' + g z θ' s)
      = (fun θ' => Work.Construction.Fstar α z θ') + (fun θ' => g z θ' s) := rfl
  simp only [Work.Spaces.pth, Ftot, slice]
  rw [hsum, deriv_add hF hg]

end Work.Stability
