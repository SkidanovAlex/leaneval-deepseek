import Mathlib
import Submission.Work.WilE3.Taylor.Grad.lagrangeOfInteriorMin
import Submission.Work.WilE3.Taylor.CaseII.aux_hasStrictFDerivAt_mul_exp_sum

namespace Work.WilE3.Taylor.CaseII

theorem hasStrictFDerivAt_sqGrad_mul_exp {k : ℕ} {Φ : (Fin k → ℝ) → ℝ} {v y u : Fin k → ℝ}
    (hΦ : ∀ z, AnalyticAt ℝ Φ z) :
    HasStrictFDerivAt
        (fun z => (∑ l, (Work.WilE3.Taylor.grad Φ z l) ^ 2) * Real.exp (∑ i, v i * (z i - y i)))
        (fderiv ℝ (fun z => (∑ l, (Work.WilE3.Taylor.grad Φ z l) ^ 2) *
          Real.exp (∑ i, v i * (z i - y i))) u) u := by
  -- The squared gradient norm `z ↦ ∑ l, (∂ₗ Φ z)²` is analytic (hence `C¹`) at `u`.
  have hS : AnalyticAt ℝ (fun z => ∑ l, (Work.WilE3.Taylor.grad Φ z l) ^ 2) u :=
    Work.WilE3.Taylor.Grad.analyticAt_grad_sqSum hΦ u
  -- Multiply by the smooth exponential factor.
  exact Work.WilE3.Taylor.CaseII.aux_hasStrictFDerivAt_mul_exp_sum
    (g := fun z => ∑ l, (Work.WilE3.Taylor.grad Φ z l) ^ 2) hS.contDiffAt

end Work.WilE3.Taylor.CaseII
