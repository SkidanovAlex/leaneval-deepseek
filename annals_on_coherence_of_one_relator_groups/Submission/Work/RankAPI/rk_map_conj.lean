import Mathlib
import Submission.Work.ORHughesFree.SylvesterRank

namespace Work.RankAPI

/-- Entrywise conjugation by a unit is multiplication on the left by the scalar (diagonal)
matrix `diag c` and on the right by `diag c⁻¹`. -/
private theorem map_conj_eq_mul {U : Type} [Ring U] (c : Uˣ) (n m : ℕ)
    (A : Matrix (Fin n) (Fin m) U) :
    A.map (fun a => (↑c : U) * a * ((c⁻¹ : Uˣ) : U))
      = (Matrix.diagonal (fun _ : Fin n => (↑c : U))) * A
        * (Matrix.diagonal (fun _ : Fin m => ((c⁻¹ : Uˣ) : U))) := by
  ext i j
  rw [Matrix.map_apply, Matrix.mul_diagonal, Matrix.diagonal_mul]

theorem rk_map_conj {U : Type} [Ring U] (rk : Work.ORHughesFree.SylvesterRank U)
    (c : Uˣ) (n m : ℕ) (A : Matrix (Fin n) (Fin m) U) :
    rk.rk n m (A.map (fun a => (↑c : U) * a * ((c⁻¹ : Uˣ) : U))) = rk.rk n m A := by
  have hL : (Matrix.diagonal (fun _ : Fin n => ((c⁻¹ : Uˣ) : U)))
      * (Matrix.diagonal (fun _ : Fin n => (↑c : U))) = 1 := by
    rw [Matrix.diagonal_mul_diagonal,
      show (fun _ : Fin n => ((c⁻¹ : Uˣ) : U) * (↑c : U)) = (fun _ => (1 : U)) from
        funext (fun _ => Units.inv_mul c),
      Matrix.diagonal_one]
  have hR : (Matrix.diagonal (fun _ : Fin m => ((c⁻¹ : Uˣ) : U)))
      * (Matrix.diagonal (fun _ : Fin m => (↑c : U))) = 1 := by
    rw [Matrix.diagonal_mul_diagonal,
      show (fun _ : Fin m => ((c⁻¹ : Uˣ) : U) * (↑c : U)) = (fun _ => (1 : U)) from
        funext (fun _ => Units.inv_mul c),
      Matrix.diagonal_one]
  have h1 := Work.ORHughesFree.SylvesterRank.rk_eq_of_left_inverse_mul rk
    (Matrix.diagonal (fun _ : Fin n => (↑c : U)))
    (Matrix.diagonal (fun _ : Fin n => ((c⁻¹ : Uˣ) : U))) hL
    (A * Matrix.diagonal (fun _ : Fin m => ((c⁻¹ : Uˣ) : U)))
  have h2 := Work.ORHughesFree.SylvesterRank.rk_eq_of_mul_right_inverse rk A
    (Matrix.diagonal (fun _ : Fin m => ((c⁻¹ : Uˣ) : U)))
    (Matrix.diagonal (fun _ : Fin m => (↑c : U))) hR
  rw [map_conj_eq_mul c n m A, Matrix.mul_assoc, h1, h2]

end Work.RankAPI
