import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.MeridianDyn.Defs
import Submission.Work.CoreResiduals.pdR_ssPsi_lam

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.MeridianDyn.Chain

theorem pdR_dynPsi {p : ℝ} {a b σ : ℝ → ℝ} {Φ : Work.FTS.MeridianDyn.Fam} {r z t : ℝ}
    (hr : 0 < r) (hb : b t ≠ 0)
    (hΦ : Work.Cyl.DiffAt2 (fun Z Θ => Φ Z Θ (σ t))
      (Work.Cyl.rhoP r z ^ p / b t) (Work.Cyl.thetaP r z)) :
    Work.Cyl.pdR (fun r' z' => Work.FTS.MeridianDyn.dynPsi p a b σ Φ r' z' t) r z
      = a t * (2 * r * Φ (Work.Cyl.rhoP r z ^ p / b t) (Work.Cyl.thetaP r z) (σ t)
          + Work.Cyl.rhoP r z ^ 2 *
              (Work.Cyl.pdR (fun Z Θ => Φ Z Θ (σ t))
                  (Work.Cyl.rhoP r z ^ p / b t) (Work.Cyl.thetaP r z)
                  * (p * (Work.Cyl.rhoP r z ^ p / b t) * (r / Work.Cyl.rhoP r z ^ 2))
                - Work.Cyl.pdZ (fun Z Θ => Φ Z Θ (σ t))
                    (Work.Cyl.rhoP r z ^ p / b t) (Work.Cyl.thetaP r z)
                    * (z / Work.Cyl.rhoP r z ^ 2))) := by
  -- `dynPsi` is the constant-rate `ssPsi` at the `σ t`-slice of `Φ`, rescaled by `a t * b t`.
  have hab : (fun r' z' => Work.FTS.MeridianDyn.dynPsi p a b σ Φ r' z' t)
      = fun r' z' => (a t * b t) * Work.CoreResiduals.ssPsi p b
          (fun Z Θ => Φ Z Θ (σ t)) r' z' t := by
    funext r' z'
    simp only [Work.FTS.MeridianDyn.dynPsi_apply, Work.CoreResiduals.ssPsi]
    field_simp
  rw [hab]
  -- a constant factor (in `r'`) pulls out of `∂_r`, unconditionally in the differentiability gap
  have hc : Work.Cyl.pdR (fun r' z' => (a t * b t) * Work.CoreResiduals.ssPsi p b
        (fun Z Θ => Φ Z Θ (σ t)) r' z' t) r z
      = (a t * b t) * Work.Cyl.pdR (fun r' z' => Work.CoreResiduals.ssPsi p b
        (fun Z Θ => Φ Z Θ (σ t)) r' z' t) r z := by
    rw [Work.Cyl.pdR, Work.Cyl.pdR]
    by_cases hc0 : (a t * b t) = 0
    · simp [hc0]
    · by_cases hd : DifferentiableAt ℝ
          (fun r' => Work.CoreResiduals.ssPsi p b (fun Z Θ => Φ Z Θ (σ t)) r' z t) r
      · rw [deriv_const_mul _ hd]
      · have hnd : ¬ DifferentiableAt ℝ (fun r' => (a t * b t) *
            Work.CoreResiduals.ssPsi p b (fun Z Θ => Φ Z Θ (σ t)) r' z t) r := by
          intro h
          apply hd
          have h1 : (fun y => (a t * b t)⁻¹ * ((a t * b t) *
                Work.CoreResiduals.ssPsi p b (fun Z Θ => Φ Z Θ (σ t)) y z t))
              = fun r' => Work.CoreResiduals.ssPsi p b (fun Z Θ => Φ Z Θ (σ t)) r' z t := by
            funext y
            rw [← mul_assoc, inv_mul_cancel₀ hc0, one_mul]
          have h2 := h.const_mul (a t * b t)⁻¹
          rwa [h1] at h2
        rw [deriv_zero_of_not_differentiableAt hnd, deriv_zero_of_not_differentiableAt hd,
          mul_zero]
  rw [hc, Work.CoreResiduals.pdR_ssPsi_lam (p := p) (lam := b)
    (Φ := fun Z Θ => Φ Z Θ (σ t)) hr hb hΦ]
  field_simp

end Work.FTS.MeridianDyn.Chain
