import Mathlib
import Submission.Work.WilE3.Taylor.Grad.lagrangeOfInteriorMin
import Submission.Work.WilE3.Taylor.CaseII.aux_fderiv_mul_exp_sum_single

namespace Work.WilE3.Taylor.CaseII

theorem grad_sqGrad_mul_exp {k : ℕ} {Φ : (Fin k → ℝ) → ℝ} {v y u : Fin k → ℝ}
    (hΦ : ∀ z, AnalyticAt ℝ Φ z) (j : Fin k) :
    Work.WilE3.Taylor.grad
        (fun z => (∑ l, (Work.WilE3.Taylor.grad Φ z l) ^ 2) * Real.exp (∑ i, v i * (z i - y i))) u j
      = Real.exp (∑ i, v i * (u i - y i)) *
          (Work.WilE3.Taylor.grad (fun z => ∑ l, (Work.WilE3.Taylor.grad Φ z l) ^ 2) u j
            + (∑ l, (Work.WilE3.Taylor.grad Φ u l) ^ 2) * v j) := by
  have hdiff : DifferentiableAt ℝ
      (fun w => ∑ l, (Work.WilE3.Taylor.grad Φ w l) ^ 2) u :=
    ((Work.WilE3.Taylor.Grad.analyticAt_grad_sqSum hΦ) u).differentiableAt
  have h := aux_fderiv_mul_exp_sum_single
    (g := fun w => ∑ l, (Work.WilE3.Taylor.grad Φ w l) ^ 2) (v := v) (y := y) hdiff j
  simp only [Work.WilE3.Taylor.grad] at h ⊢
  rw [h]
  ring

end Work.WilE3.Taylor.CaseII
