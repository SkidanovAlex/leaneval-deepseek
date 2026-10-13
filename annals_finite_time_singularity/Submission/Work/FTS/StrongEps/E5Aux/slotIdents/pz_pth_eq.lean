import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.InnerProductSpace.Basic
import Submission.Work.Spaces.Defs
import Submission.Work.Spaces.mixed_comm

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.E5Aux.slotIdents

/-- `∂_z ∂_θ` versus the mixed operator: `mixed 1 1 u = D_z(D_θ u) = z · ∂_z(sin(2θ)·∂_θu)`,
and the factor `sin(2θ)` is constant in `z`, so the mixed derivative is `z · sin(2θ) · ∂_z∂_θ u`. -/
theorem pz_pth_eq {u : ℝ → ℝ → ℝ} {z θ : ℝ}
    (h : ContDiffAt ℝ 2 (Function.uncurry u) (z, θ)) (hz : z ≠ 0)
    (hs : Real.sin (2 * θ) ≠ 0) :
    Work.Spaces.pz (Work.Spaces.pth u) z θ
      = Work.Spaces.mixed 1 1 u z θ / (z * Real.sin (2 * θ)) := by
  -- `mixed 1 1 u = Dz (Dth u) = z · ∂_z(D_θ u)` definitionally.
  have hmix : Work.Spaces.mixed 1 1 u z θ
      = z * Work.Spaces.pz (Work.Spaces.Dth u) z θ := rfl
  -- The `θ`-slice factor `sin(2θ)` is constant in `z`, so it comes out of the derivative.
  have h1 : Work.Spaces.pz (Work.Spaces.Dth u) z θ
      = Real.sin (2 * θ) * Work.Spaces.pz (Work.Spaces.pth u) z θ := by
    show deriv (fun z' => Real.sin (2 * θ) * Work.Spaces.pth u z' θ) z
      = Real.sin (2 * θ) * deriv (fun z' => Work.Spaces.pth u z' θ) z
    rw [deriv_const_mul_field]
  rw [hmix, h1, eq_div_iff (mul_ne_zero hz hs)]
  ring

end Work.FTS.StrongEps.E5Aux.slotIdents
