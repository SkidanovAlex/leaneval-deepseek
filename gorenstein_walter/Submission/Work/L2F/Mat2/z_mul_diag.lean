import Mathlib
import Submission.Work.L2F.Defs

namespace Work.L2F.Mat2

theorem z_mul_diag (F : Type*) [Field F] (a : Fˣ) :
    Work.L2F.z F * Work.PSL2.diag F a = Work.PSL2.diag F a⁻¹ * Work.L2F.z F := by
  apply Subtype.ext
  simp only [Work.L2F.z, Work.PSL2.coe_diag, Work.PSL2.coe_weyl,
    Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

end Work.L2F.Mat2
