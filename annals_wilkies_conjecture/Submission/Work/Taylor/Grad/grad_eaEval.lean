import Mathlib
import Submission.Work.WilE3.Defs
import Submission.Work.WilE3.Taylor.Polar.Basic
import Submission.Work.WilE3.API.hasFDerivAt_eaEval

namespace Work.Taylor.Grad

theorem grad_eaEval {k r : ℕ} (c : WilkiesDesign.E.EAChain k r) (Q : WilkiesDesign.E.EAPoly k r)
    (x : Fin k → ℝ) (i : Fin k) :
    Work.WilE3.Taylor.grad (fun z : Fin k → ℝ => WilkiesDesign.E.eaEval c Q z) x i
      = WilkiesDesign.E.eaEval c (WilkiesDesign.E.eaD c i Q) x := by
  have h := Work.WilE3.API.hasFDerivAt_eaEval c Q x
  rw [Work.WilE3.Taylor.grad, h.fderiv]
  simp only [sum_apply, smul_apply, ContinuousLinearMap.proj_apply, smul_eq_mul]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hj
    rw [Pi.single_eq_of_ne hj, mul_zero]
  · intro hi
    exact absurd (Finset.mem_univ i) hi

end Work.Taylor.Grad
