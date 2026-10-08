import Mathlib

namespace Work.L2F.Mat2

theorem det_smul_one_add_smul (F : Type*) [Field F] (X : Matrix (Fin 2) (Fin 2) F) (a b : F) :
    (a • 1 + b • X).det = a ^ 2 + a * b * X.trace + b ^ 2 * X.det := by
  rw [Matrix.det_fin_two, Matrix.trace_fin_two, Matrix.det_fin_two]
  simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply]
  norm_num
  ring

end Work.L2F.Mat2
