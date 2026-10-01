import Mathlib
import Submission.Work.ZeroFreeTables.testFn71_defs
import Submission.Work.ZeroFreeTables.tf71Fc_model
import Submission.Work.ZeroFreeTables.tf71Fc_differentiable_cf
import Submission.Work.ZeroFreeTables.tf71Fc_decay

namespace Work.ZeroFreeTables

/-- `tf71Fc` is, on its interval of integration, the Laplace transform of the *continuous*
model `tf71cfC` over the fixed interval `[0, 2γ]`; hence it is continuous on all of `ℂ`
(parametric interval integral of a continuous integrand). -/
theorem tf71Fc_continuous {θ lam : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < Real.pi / 2)
    (hlam : 0 < lam) : Continuous (tf71Fc θ lam) := by
  have hcont : Continuous (fun z : ℂ => ∫ t in (0:ℝ)..(2 * tf71γ θ lam),
      Complex.exp (-(z * (t:ℂ))) * tf71cfC θ lam t) := by
    apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    show Continuous (Function.uncurry (fun (z : ℂ) (t : ℝ) =>
      Complex.exp (-(z * (t:ℂ))) * tf71cfC θ lam t))
    have hcf := tf71cfC_cont θ lam
    fun_prop
  refine hcont.congr ?_
  intro z
  exact (tf71Fc_eq_integral_cf hθ0 hθ1 hlam z).symm

theorem tf71Fc_continuousOn (θ lam : ℝ) (hθ0 : 0 < θ) (hθ1 : θ < Real.pi / 2)
    (hlam : 0 < lam) :
    ContinuousOn (Work.ZeroFreeTables.tf71Fc θ lam) {z : ℂ | 0 ≤ z.re} :=
  (tf71Fc_continuous hθ0 hθ1 hlam).continuousOn

theorem tf71Fc_analytic (θ lam : ℝ) (hθ0 : 0 < θ) (hθ1 : θ < Real.pi / 2) (hlam : 0 < lam) :
    DifferentiableOn ℂ (Work.ZeroFreeTables.tf71Fc θ lam) {z : ℂ | 0 ≤ z.re} ∧
    ContinuousOn (Work.ZeroFreeTables.tf71Fc θ lam) {z : ℂ | 0 ≤ z.re} ∧
    (∀ ε : ℝ, 0 < ε → ∃ R : ℝ, 0 < R ∧ ∀ z : ℂ, 0 ≤ z.re → R ≤ ‖z‖ →
      ‖Work.ZeroFreeTables.tf71Fc θ lam z‖ < ε) := by
  refine ⟨?_, tf71Fc_continuousOn θ lam hθ0 hθ1 hlam, fun ε hε =>
    tf71Fc_decay θ lam hθ0 hθ1 hlam ε hε⟩
  rw [show tf71Fc θ lam = (fun z : ℂ => ∫ t in (0:ℝ)..(2 * tf71γ θ lam),
      Complex.exp (-(z * (t:ℂ))) * tf71cfC θ lam t) from
    funext (fun z => tf71Fc_eq_integral_cf hθ0 hθ1 hlam z)]
  exact (tf71Fc_differentiable_cf θ lam hθ0 hθ1 hlam).differentiableOn

end Work.ZeroFreeTables
