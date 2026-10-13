import Mathlib.Analysis.Calculus.Deriv.CompMul
import Mathlib.Analysis.InnerProductSpace.PiL2
import Submission.Work.FTS.PressureOn.Defs
import Submission.Work.FTS.PressureOn.PoissonAux.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PressureOn.PoissonAux.KI

/-- The one-dimensional profiles are related by the scaling
`ρ_ε(r) = ρ_1(r/ε)`, i.e. `rhoProfile ε = fun r => rhoProfile 1 (ε⁻¹ * r)`. -/
theorem rhoProfile_scale (ε : ℝ) (r : ℝ) :
    rhoProfile ε r = rhoProfile 1 (ε⁻¹ * r) := by
  rw [rhoProfile_apply, rhoProfile_apply]
  norm_num
  congr 1
  rw [mul_pow, inv_pow, div_eq_mul_inv]
  ring

/-- The first derivative of `rhoProfile` scales as expected. -/
theorem deriv_rhoProfile_scale (ε : ℝ) :
    deriv (rhoProfile ε) = fun r => ε⁻¹ * deriv (rhoProfile 1) (ε⁻¹ * r) := by
  rw [show rhoProfile ε = fun r => rhoProfile 1 (ε⁻¹ * r) from funext (rhoProfile_scale ε)]
  funext r
  rw [deriv_comp_mul_left]
  simp [smul_eq_mul]

/-- The second derivative of `rhoProfile` scales as expected: `ρ_ε''(r) = ε⁻² ρ_1''(r/ε)`. -/
theorem deriv_deriv_rhoProfile_scale (ε : ℝ) :
    deriv (deriv (rhoProfile ε))
      = fun r => ε⁻¹ * (ε⁻¹ * deriv (deriv (rhoProfile 1)) (ε⁻¹ * r)) := by
  rw [deriv_rhoProfile_scale ε]
  funext r
  change deriv (fun x => (fun s => ε⁻¹ * deriv (rhoProfile 1) s) (ε⁻¹ * x)) r =
    ε⁻¹ * (ε⁻¹ * deriv (deriv (rhoProfile 1)) (ε⁻¹ * r))
  have h := deriv_comp_mul_left (ε⁻¹) (fun s => ε⁻¹ * deriv (rhoProfile 1) s) r
  rw [h]
  rw [deriv_const_mul_field]
  simp [smul_eq_mul]

/-- The Newtonian kernel is homogeneous of degree `-1`: `newtonKernel (ε⁻¹ • x) = ε * newtonKernel x`
for `ε > 0`. -/
theorem newtonKernel_scale {ε : ℝ} (hε : 0 < ε) (x : R3) :
    newtonKernel (ε⁻¹ • x) = ε * newtonKernel x := by
  simp only [newtonKernel]
  rw [norm_smul, Real.norm_of_nonneg (by positivity)]
  field_simp

/-- Scaling of the norm under `ε⁻¹ • ·` for `ε > 0`. -/
theorem norm_inv_smul {ε : ℝ} (hε : 0 < ε) (x : R3) : ‖ε⁻¹ • x‖ = ε⁻¹ * ‖x‖ := by
  rw [norm_smul, Real.norm_of_nonneg (by positivity)]

/-- **Scaling of the mass kernel.** The mass kernel `massKernel ε x = (4π‖x‖)⁻¹ ρ_ε''(‖x‖)` is
homogeneous of degree `-3` in the scaling parameter: `massKernel ε = ε⁻³ (massKernel 1)(·/ε)`,
i.e. `massKernel ε x = (ε³)⁻¹ * massKernel 1 (ε⁻¹ • x)` for `ε > 0`. -/
theorem massKernel_scale (ε : ℝ) (hε : 0 < ε) (x : R3) :
    massKernel ε x = (ε ^ 3)⁻¹ * massKernel 1 (ε⁻¹ • x) := by
  rw [massKernel_eq, massKernel_eq, deriv_deriv_rhoProfile_scale ε]
  rw [newtonKernel_scale hε x, norm_inv_smul hε x]
  field_simp

end Work.FTS.PressureOn.PoissonAux.KI
