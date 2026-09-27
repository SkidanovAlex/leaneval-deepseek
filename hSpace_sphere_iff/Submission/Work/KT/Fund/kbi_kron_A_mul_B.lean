import Mathlib

namespace Work.KT.Fund

open Matrix

theorem kbi_kron_A_mul_B {R : Type} [Ring R] {n : ℕ} (P : Matrix (Fin n) (Fin n) R) :
    (Matrix.of fun (j : Fin n) (x : Fin n × Fin 2) => if x.2 = 0 then P j x.1 else 0) *
      (Matrix.of fun (x : Fin n × Fin 2) (j : Fin n) => if x.2 = 0 then P x.1 j else 0)
    = P * P := by
  ext j k
  simp only [Matrix.mul_apply, Matrix.of_apply]
  rw [Fintype.sum_prod_type]
  simp only [Fin.sum_univ_two, Fin.isValue]
  simp

end Work.KT.Fund
