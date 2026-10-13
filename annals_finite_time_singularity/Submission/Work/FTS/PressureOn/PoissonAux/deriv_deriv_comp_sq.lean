import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Topology.Algebra.Module.ModuleTopology

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PressureOn.PoissonAux

theorem deriv_deriv_comp_sq (F : ℝ → ℝ) (hF : ContDiff ℝ 2 F) {ρ : ℝ} (hρ : 0 < ρ) :
    deriv (deriv (fun r : ℝ => F (r ^ 2))) ρ + 2 * deriv (fun r : ℝ => F (r ^ 2)) ρ / ρ
      = 6 * deriv F (ρ ^ 2) + 4 * ρ ^ 2 * deriv (deriv F) (ρ ^ 2) := by
  have hDiffF : Differentiable ℝ F := hF.differentiable (by norm_num)
  have hDiffdF : Differentiable ℝ (deriv F) := hF.differentiable_deriv_two
  -- First derivative: `deriv (fun r => F (r^2)) = fun r => 2 * r * deriv F (r^2)`.
  have hGfun : deriv (fun r : ℝ => F (r ^ 2)) = fun r => 2 * r * deriv F (r ^ 2) := by
    funext r
    have h1 : HasDerivAt (fun s : ℝ => s ^ 2) (2 * r) r := by
      simpa using hasDerivAt_pow 2 r
    have h2 : HasDerivAt F (deriv F (r ^ 2)) (r ^ 2) :=
      (hDiffF.differentiableAt (x := r ^ 2)).hasDerivAt
    have h3 : HasDerivAt (fun s : ℝ => F (s ^ 2)) (deriv F (r ^ 2) * (2 * r)) r :=
      h2.comp_of_eq r h1 rfl
    rw [h3.deriv]; ring
  -- Second derivative at `ρ`.
  have hH : deriv (deriv (fun r : ℝ => F (r ^ 2))) ρ
      = 2 * deriv F (ρ ^ 2) + 4 * ρ ^ 2 * deriv (deriv F) (ρ ^ 2) := by
    rw [hGfun]
    have h1 : HasDerivAt (fun s : ℝ => s ^ 2) (2 * ρ) ρ := by
      simpa using hasDerivAt_pow 2 ρ
    have h2 : HasDerivAt (deriv F) (deriv (deriv F) (ρ ^ 2)) (ρ ^ 2) :=
      (hDiffdF.differentiableAt (x := ρ ^ 2)).hasDerivAt
    have h3 : HasDerivAt (fun s : ℝ => deriv F (s ^ 2))
        (deriv (deriv F) (ρ ^ 2) * (2 * ρ)) ρ := h2.comp_of_eq ρ h1 rfl
    have h4 : HasDerivAt (fun s : ℝ => 2 * s) 2 ρ := by
      simpa using (hasDerivAt_id ρ).const_mul 2
    have h5 : HasDerivAt (fun s : ℝ => 2 * s * deriv F (s ^ 2))
        (2 * deriv F (ρ ^ 2) + (2 * ρ) * (deriv (deriv F) (ρ ^ 2) * (2 * ρ))) ρ :=
      h4.mul h3
    rw [h5.deriv]; ring
  rw [hH, hGfun]
  have hρne : ρ ≠ 0 := ne_of_gt hρ
  field_simp
  ring

end Work.FTS.PressureOn.PoissonAux
