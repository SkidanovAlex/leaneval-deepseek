import Mathlib
import Submission.Work.L2F.Defs

namespace Work.L2F.Mat2

/-- For `G ∈ SL(2,F)` and `b : F`, the `(1,0)`-entry of the conjugate `G⁻¹ * unipotent b * G`
is `-(G 1 0)^2 * b`: writing `G = !![p,q;r,s]`, the conjugate is
`!![1 + s*r*b, s^2*b; -r^2*b, 1 - r*s*b]`, whose `(1,0)`-entry is `-r^2*b`. -/
theorem conj_unipotent_entry (F : Type*) [Field F] (G : Matrix.SpecialLinearGroup (Fin 2) F)
    (b : F) :
    ((G⁻¹ * Work.PSL2.unipotent F b * G : Matrix.SpecialLinearGroup (Fin 2) F) :
        Matrix (Fin 2) (Fin 2) F) 1 0
      = -(((G : Matrix (Fin 2) (Fin 2) F) 1 0)^2) * b := by
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
    Matrix.SpecialLinearGroup.coe_inv, Work.PSL2.coe_unipotent]
  rw [Matrix.adjugate_fin_two, Matrix.eta_fin_two (G : Matrix (Fin 2) (Fin 2) F)]
  rw [Matrix.mul_fin_two, Matrix.mul_fin_two]
  simp
  ring

end Work.L2F.Mat2
