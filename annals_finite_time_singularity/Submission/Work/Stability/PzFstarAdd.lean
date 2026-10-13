import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.InnerProductSpace.Basic
import Submission.Work.Stability.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.Stability

/-- The `z`-slice of the reference profile `F_* = α(Γ/c)·F_{*,rad}` is differentiable at every
`z > -1`: `F_{*,rad}(z) = 2z/(1+z)²` is a rational function whose only pole is at `z = -1`
(`Work.FM.hasDerivAt_Fstar`), and the angular factor `α(Γ(θ)/c)` is a constant of the slice. -/
theorem differentiableAt_Fstar_slice (α θ z : ℝ) (hz : -1 < z) :
    DifferentiableAt ℝ (fun z' => Work.Construction.Fstar α z' θ) z := by
  have h := (Work.FM.hasDerivAt_Fstar z hz).differentiableAt.const_mul
    (α * (Work.Spaces.Gam α θ / Work.Spaces.c α))
  simpa [Work.Construction.Fstar, mul_assoc] using h

/-- The `z`-derivative of the full profile `F = F_* + g` splits: `∂_z(F_* + g) = ∂_zF_* + ∂_zg`
whenever the slice of `g` is differentiable at `z`.  (`-1 < z` is exactly the differentiability
range of the profile's `z`-slice `2z/(1+z)²`; on the open quadrant `Qd` it holds automatically.)
This discharges the `hDz`-field of `Work.Stability.GDerivData`. -/
theorem PzFstarAdd {α : ℝ} {g : F3} {z θ s : ℝ} (hz : -1 < z)
    (hg : DifferentiableAt ℝ (fun z' => g z' θ s) z) :
    Work.Spaces.pz (fun z' θ' => Ftot α g s z' θ') z θ
      = Work.Spaces.pz (Work.Construction.Fstar α) z θ + Work.Spaces.pz (slice g s) z θ := by
  have hF : DifferentiableAt ℝ (fun z' => Work.Construction.Fstar α z' θ) z :=
    differentiableAt_Fstar_slice α θ z hz
  have hsum : (fun z' => Work.Construction.Fstar α z' θ + g z' θ s)
      = (fun z' => Work.Construction.Fstar α z' θ) + (fun z' => g z' θ s) := rfl
  simp only [Work.Spaces.pz, Ftot, slice]
  rw [hsum, deriv_add hF hg]

end Work.Stability
