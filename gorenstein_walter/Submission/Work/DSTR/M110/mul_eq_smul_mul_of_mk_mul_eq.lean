import Mathlib

namespace Work.DSTR.M110

lemma mul_eq_smul_mul_of_mk_mul_eq {F : Type*} [Field F]
    (A B : Matrix.GeneralLinearGroup (Fin 2) F)
    (h : Matrix.ProjGenLinGroup.mk B * Matrix.ProjGenLinGroup.mk A =
      Matrix.ProjGenLinGroup.mk A * Matrix.ProjGenLinGroup.mk B) :
    ∃ u : Fˣ, (A : Matrix (Fin 2) (Fin 2) F) * (B : Matrix (Fin 2) (Fin 2) F) =
      (u : F) • ((B : Matrix (Fin 2) (Fin 2) F) * (A : Matrix (Fin 2) (Fin 2) F)) := by
  have hBA : Matrix.ProjGenLinGroup.mk (B * A) = Matrix.ProjGenLinGroup.mk (A * B) := by
    rw [map_mul, map_mul]; exact h
  obtain ⟨u, hu⟩ := Matrix.ProjGenLinGroup.mk_eq_mk_iff.mp hBA
  refine ⟨u, ?_⟩
  have hmat : (B : Matrix (Fin 2) (Fin 2) F) * (A : Matrix (Fin 2) (Fin 2) F)
      * Matrix.scalar (Fin 2) (u : F) =
      (A : Matrix (Fin 2) (Fin 2) F) * (B : Matrix (Fin 2) (Fin 2) F) := by
    have hc := congrArg
      (fun g : Matrix.GeneralLinearGroup (Fin 2) F => (g : Matrix (Fin 2) (Fin 2) F)) hu
    simpa [Matrix.GeneralLinearGroup.coe_mul, Matrix.GeneralLinearGroup.coe_scalar] using hc
  rw [← hmat]
  rw [show Matrix.scalar (Fin 2) (u : F) = (u : F) • (1 : Matrix (Fin 2) (Fin 2) F) from by
        rw [Matrix.scalar_apply, ← Matrix.smul_one_eq_diagonal]]
  rw [Matrix.mul_smul, mul_one]

end Work.DSTR.M110
