import Submission.Commons.Analysis.Calculus.Laplacian.laplacian_comp_norm
import Submission.Commons.Analysis.Asymptotics.growth_fderiv2_logLaplace

namespace Commons.Analysis.Calculus.FDeriv

open scoped RealInnerProductSpace

open scoped RealInnerProductSpace in
theorem fderiv_fderiv_radial {ψ : ℝ → ℝ} {r : ℝ} (hr : 0 < r) (hψ : ContDiffAt ℝ 2 ψ r)
    (x v : EuclideanSpace ℝ (Fin 4)) (hx : ‖x‖ = r) :
    (fderiv ℝ (fderiv ℝ (fun y : EuclideanSpace ℝ (Fin 4) => ψ ‖y‖)) x) v v
      = deriv (deriv ψ) r * (⟪v, x⟫ / r) ^ 2
        + (deriv ψ r / r) * (‖v‖ ^ 2 - (⟪v, x⟫ / r) ^ 2) := by
  have hxne : x ≠ 0 := by
    rw [← norm_pos_iff, hx]; exact hr
  have hψ' : ContDiffAt ℝ 2 ψ ‖x‖ := by rw [hx]; exact hψ
  rw [Commons.Analysis.Asymptotics.fderiv_fderiv_eq_iteratedFDeriv
    (fun y : EuclideanSpace ℝ (Fin 4) => ψ ‖y‖) x v]
  rw [Commons.Analysis.Calculus.Laplacian.iteratedFDeriv_two_comp_norm_apply hxne hψ' v]
  rw [hx, ← real_inner_comm x v]
  have hrne : r ≠ 0 := ne_of_gt hr
  field_simp

end Commons.Analysis.Calculus.FDeriv
