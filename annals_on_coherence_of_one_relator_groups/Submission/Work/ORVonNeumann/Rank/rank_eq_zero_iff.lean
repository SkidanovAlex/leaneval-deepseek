import Mathlib
import Submission.Work.ORVonNeumann.SylvesterRank

namespace Work.ORVonNeumann.Rank

open Matrix

/-- A single entry `A i j` of a matrix is a product `(e * A) * f` of a `1 × n` row vector
`e`, `A` and an `n × 1` column vector `f`, so `!![A i j]` has rank at most `rk A`. -/
private lemma rank_entry_le {R : Type*} [Ring R] (rk : Work.ORVonNeumann.SylvesterRankFunction R)
    {m n : ℕ} (A : Matrix (Fin m) (Fin n) R) (i : Fin m) (j : Fin n) :
    rk.rank (!![A i j] : Matrix (Fin 1) (Fin 1) R) ≤ rk.rank A := by
  have hsplit :
      (Matrix.of (fun (_ : Fin 1) (k : Fin m) => if k = i then (1 : R) else 0) * A
          * Matrix.of (fun (k : Fin n) (_ : Fin 1) => if k = j then (1 : R) else 0))
        = (!![A i j] : Matrix (Fin 1) (Fin 1) R) := by
    ext p q
    fin_cases p; fin_cases q
    simp only [Matrix.mul_apply, Matrix.of_apply, Matrix.cons_val_fin_one]
    simp only [ite_mul, zero_mul, mul_ite, mul_one, mul_zero, one_mul]
    simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
  have h1 : rk.rank (!![A i j] : Matrix (Fin 1) (Fin 1) R)
      ≤ rk.rank (Matrix.of (fun (_ : Fin 1) (k : Fin m) => if k = i then (1 : R) else 0) * A) := by
    rw [← hsplit]
    exact rk.rank_mul_le_left _ _
  have h2 : rk.rank (Matrix.of (fun (_ : Fin 1) (k : Fin m) => if k = i then (1 : R) else 0) * A)
      ≤ rk.rank A := rk.rank_mul_le_right _ _
  exact le_trans h1 h2

/-- For a faithful Sylvester rank function, a matrix has rank `0` exactly when it is the
zero matrix.  If `rk A = 0` then every entry `A i j` has rank `0`, since `!![A i j]` is a
product involving `A`; faithfulness then forces `A i j = 0`. -/
theorem rank_eq_zero_iff {R : Type*} [Ring R] (rk : Work.ORVonNeumann.SylvesterRankFunction R) (h : rk.Faithful) {m n : ℕ} (A : Matrix (Fin m) (Fin n) R) : rk.rank A = 0 ↔ A = 0 := by
  refine ⟨fun hA => ?_, fun hA => by rw [hA]; simp⟩
  ext i j
  have hle := rank_entry_le rk A i j
  rw [hA] at hle
  exact h (A i j) (le_antisymm hle (rk.rank_nonneg (!![A i j] : Matrix (Fin 1) (Fin 1) R)))

end Work.ORVonNeumann.Rank
