import Mathlib

namespace Work.DSTR.M110

/-- Matrix-level core: if `a * b = u • (b * a)` and `u * u = 1`, then `a²` commutes
with `b`.  No invertibility is needed once `u * u = 1` is known. -/
private lemma mul_sq_eq_of_smul_comm {F : Type*} [Field F]
    {a b : Matrix (Fin 2) (Fin 2) F} {u : F}
    (h : a * b = u • (b * a)) (hu : u * u = 1) :
    (a * a) * b = b * (a * a) := by
  calc (a * a) * b = a * (a * b) := by rw [mul_assoc]
    _ = a * (u • (b * a)) := by rw [h]
    _ = u • (a * (b * a)) := by rw [Matrix.mul_smul]
    _ = u • ((a * b) * a) := by rw [mul_assoc]
    _ = u • ((u • (b * a)) * a) := by rw [h]
    _ = u • (u • ((b * a) * a)) := by rw [Matrix.smul_mul]
    _ = u • (u • (b * (a * a))) := by rw [mul_assoc]
    _ = (u * u) • (b * (a * a)) := by rw [smul_smul]
    _ = b * (a * a) := by rw [hu, one_smul]

lemma sq_mul_eq_mul_sq_of_smul_twist {F : Type*} [Field F]
    (A B : Matrix.GeneralLinearGroup (Fin 2) F) (u : Fˣ)
    (h : (A : Matrix (Fin 2) (Fin 2) F) * (B : Matrix (Fin 2) (Fin 2) F) =
      (u : F) • ((B : Matrix (Fin 2) (Fin 2) F) * (A : Matrix (Fin 2) (Fin 2) F))) :
    ((A * A : Matrix.GeneralLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) *
        (B : Matrix (Fin 2) (Fin 2) F) =
      (B : Matrix (Fin 2) (Fin 2) F) *
        ((A * A : Matrix.GeneralLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) := by
  -- Determinant argument: taking determinants of `A * B = u • (B * A)` forces `u ^ 2 = 1`.
  have hdet : (A : Matrix (Fin 2) (Fin 2) F).det * (B : Matrix (Fin 2) (Fin 2) F).det =
      (u : F) ^ 2 *
        ((A : Matrix (Fin 2) (Fin 2) F).det * (B : Matrix (Fin 2) (Fin 2) F).det) := by
    have h1 := congrArg Matrix.det h
    rw [Matrix.det_mul, Matrix.det_smul, Fintype.card_fin, Matrix.det_mul] at h1
    rwa [mul_comm (B : Matrix (Fin 2) (Fin 2) F).det
      (A : Matrix (Fin 2) (Fin 2) F).det] at h1
  have hd : (A : Matrix (Fin 2) (Fin 2) F).det * (B : Matrix (Fin 2) (Fin 2) F).det ≠ 0 :=
    mul_ne_zero (Matrix.GeneralLinearGroup.det_ne_zero A)
      (Matrix.GeneralLinearGroup.det_ne_zero B)
  have hu2 : (u : F) ^ 2 = 1 := by
    have h2 : (A : Matrix (Fin 2) (Fin 2) F).det * (B : Matrix (Fin 2) (Fin 2) F).det * 1 =
        (A : Matrix (Fin 2) (Fin 2) F).det * (B : Matrix (Fin 2) (Fin 2) F).det *
          (u : F) ^ 2 := by
      rw [mul_one, mul_comm ((A : Matrix (Fin 2) (Fin 2) F).det *
        (B : Matrix (Fin 2) (Fin 2) F).det) ((u : F) ^ 2)]
      exact hdet
    exact (mul_left_cancel₀ hd h2).symm
  have hu : (u : F) * (u : F) = 1 := by rw [← pow_two]; exact hu2
  have main := mul_sq_eq_of_smul_comm (a := (A : Matrix (Fin 2) (Fin 2) F))
    (b := (B : Matrix (Fin 2) (Fin 2) F)) (u := (u : F)) h hu
  rw [Matrix.GeneralLinearGroup.coe_mul]
  exact main

end Work.DSTR.M110
