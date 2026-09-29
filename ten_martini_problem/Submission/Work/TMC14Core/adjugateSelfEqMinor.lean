import Mathlib

namespace Work.TMC14Core

/-- Replacing row `i` of `A` by row `i` of the identity matrix is the same as updating
row `i` of `A` with the coordinate vector `Pi.single i 1`. -/
private lemma of_piecewise_singleton_row {R : Type*} [CommRing R] {n : ℕ}
    (A : Matrix (Fin n) (Fin n) R) (i : Fin n) :
    (Matrix.of (({i} : Finset (Fin n)).piecewise (1 : Matrix (Fin n) (Fin n) R).row A.row))
      = A.updateRow i (Pi.single i 1) := by
  ext k j
  rw [Matrix.updateRow_apply]
  by_cases hk : k = i
  · subst hk
    rw [if_pos rfl]
    have h1 : (1 : Matrix (Fin n) (Fin n) R).row k = Pi.single k 1 := by
      funext j
      simp [Matrix.one_apply, Pi.single_apply, eq_comm]
    rw [← h1]
    simp [Finset.piecewise, Matrix.row]
  · rw [if_neg hk]
    simp [Finset.piecewise, Matrix.row, hk]

theorem adjugateSelfEqMinor {R : Type*} [CommRing R] {n : ℕ} (A : Matrix (Fin n) (Fin n) R) (i : Fin n) :
    (Matrix.adjugate A) i i
      = (Matrix.of (({i} : Finset (Fin n)).piecewise (1 : Matrix (Fin n) (Fin n) R).row A.row)).det := by
  rw [Matrix.adjugate_apply, of_piecewise_singleton_row]

end Work.TMC14Core
