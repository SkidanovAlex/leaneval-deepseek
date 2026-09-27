import Mathlib
import Submission.Work.EKLContract.Lemmas.isHoro_Uij
import Submission.Work.EKLContract.Interfaces

namespace Work.EKLC6Core

/-- A diagonal matrix commutes with the transvection `1 + s · E_ij` whenever the two
diagonal entries used, `d i` and `d j`, coincide.

The transvection `transvection i j s` is `1 + single i j s`, so it suffices to commute
`diagonal d` past `single i j s`.  Multiplying on the left picks up the row index (`d i`),
multiplying on the right picks up the column index (`d j`), whence the hypothesis `d i = d j`. -/
private lemma diagonal_mul_transvection_comm {n : Type*} [DecidableEq n] [Fintype n]
    {i j : n} (d : n → ℝ) (hd : d i = d j) (s : ℝ) :
    Matrix.diagonal d * Matrix.transvection i j s
      = Matrix.transvection i j s * Matrix.diagonal d := by
  have h1 : Matrix.diagonal d * Matrix.single i j s = Matrix.single i j (d i * s) := by
    ext a b
    rw [Matrix.diagonal_mul]
    simp only [Matrix.single, Matrix.of_apply]
    by_cases hc : i = a ∧ j = b
    · obtain ⟨rfl, rfl⟩ := hc; simp
    · rw [if_neg hc, if_neg hc]; simp
  have h2 : Matrix.single i j s * Matrix.diagonal d = Matrix.single i j (s * d j) := by
    ext a b
    rw [Matrix.mul_diagonal]
    simp only [Matrix.single, Matrix.of_apply]
    by_cases hc : i = a ∧ j = b
    · obtain ⟨rfl, rfl⟩ := hc; simp
    · rw [if_neg hc, if_neg hc]; simp
  show Matrix.diagonal d * (1 + Matrix.single i j s)
      = (1 + Matrix.single i j s) * Matrix.diagonal d
  rw [mul_add, add_mul, mul_one, one_mul, h1, h2]
  congr 1
  rw [hd, mul_comm]

theorem aDiag_mul_uij_of_eq {i j : Fin 3} (h : i ≠ j) (t : Fin 3 → ℝ) (ht : t i = t j) (s : ℝ) :
    Work.EKLContract.aDiag t * Work.EKLContract.uij h s
      = Work.EKLContract.uij h s * Work.EKLContract.aDiag t := by
  apply Subtype.ext
  simp only [Matrix.SpecialLinearGroup.coe_mul]
  exact diagonal_mul_transvection_comm
    (fun k => Real.exp (t k - (∑ j, t j) / 3)) (by simp [ht]) s

end Work.EKLC6Core
