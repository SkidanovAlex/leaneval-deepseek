import Mathlib
import Submission.Work.L2F.Mat2.sq_eq_trace_smul_sub_det

namespace Work.L2F.Props.oddsub

theorem eval_mul_coeff (F L : Type*) [Field F] [Field L] [Algebra F L]
    (t : Matrix (Fin 2) (Fin 2) F) (lam : L)
    (hlam : lam ^ 2 = algebraMap F L t.trace * lam - algebraMap F L t.det) (a b c d : F) :
    (a • (1 : Matrix (Fin 2) (Fin 2) F) + b • t) * (c • 1 + d • t)
        = (a * c - b * d * t.det) • 1 + (a * d + b * c + b * d * t.trace) • t ∧
      (algebraMap F L a + algebraMap F L b * lam) * (algebraMap F L c + algebraMap F L d * lam)
        = algebraMap F L (a * c - b * d * t.det)
            + algebraMap F L (a * d + b * c + b * d * t.trace) * lam := by
  refine ⟨?_, ?_⟩
  · -- matrix identity: check entries and expand
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply,
        Matrix.trace_fin_two, Matrix.det_fin_two, Fin.sum_univ_two] <;> ring
  · -- algebra identity: use `lam ^ 2 = trace * lam - det`
    have expand :
        (algebraMap F L a + algebraMap F L b * lam) *
            (algebraMap F L c + algebraMap F L d * lam)
          = algebraMap F L a * algebraMap F L c
            + (algebraMap F L a * algebraMap F L d + algebraMap F L b * algebraMap F L c) * lam
            + algebraMap F L b * algebraMap F L d * lam ^ 2 := by
      ring
    rw [expand, hlam]
    simp only [map_sub, map_add, map_mul]
    ring

end Work.L2F.Props.oddsub
