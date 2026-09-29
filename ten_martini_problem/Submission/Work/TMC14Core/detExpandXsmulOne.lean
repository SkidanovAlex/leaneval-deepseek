import Mathlib

namespace Work.TMC14Core

open Matrix

/-- Expansion of `det (P + Q)` by multilinearity of the determinant in the rows: choosing for each
row either the corresponding row of `Q` (indices in `t`) or of `P` (indices outside `t`). -/
theorem detExpandXsmulOne_aux_add {S : Type*} [CommRing S] {n : ℕ}
    (P Q : Matrix (Fin n) (Fin n) S) :
    (P + Q).det = ∑ t : Finset (Fin n), (Matrix.of (t.piecewise Q P)).det := by
  classical
  have h := (Matrix.detRowAlternating (R := S) (n := Fin n)).map_add_univ Q P
  rw [add_comm P Q]
  simp only [Matrix.det] at h ⊢
  exact h

/-- Factoring the scalar `∏ i ∈ t, c i` out of the rows indexed by `t`. -/
theorem detExpandXsmulOne_aux_smul {S : Type*} [CommRing S] {n : ℕ}
    (c : Fin n → S) (u : Matrix (Fin n) (Fin n) S) (t : Finset (Fin n)) :
    (Matrix.of (t.piecewise (fun i => c i • u i) u)).det = (∏ i ∈ t, c i) * u.det := by
  classical
  have h := (Matrix.detRowAlternating (R := S) (n := Fin n)).map_piecewise_smul c u t
  simp only [Matrix.det, smul_eq_mul] at h ⊢
  exact h

theorem detExpandXsmulOne {R : Type*} [CommRing R] {n : ℕ} (A : Matrix (Fin n) (Fin n) R) :
    (A.map Polynomial.C + (Polynomial.X : Polynomial R) • (1 : Matrix (Fin n) (Fin n) (Polynomial R))).det
      = ∑ t : Finset (Fin n),
          (Polynomial.X : Polynomial R) ^ t.card *
            Polynomial.C ((Matrix.of (t.piecewise (1 : Matrix (Fin n) (Fin n) R).row A.row)).det) := by
  classical
  rw [detExpandXsmulOne_aux_add (A.map Polynomial.C)
        ((Polynomial.X : Polynomial R) • (1 : Matrix (Fin n) (Fin n) (Polynomial R)))]
  refine Finset.sum_congr rfl (fun t _ => ?_)
  set E : Matrix (Fin n) (Fin n) R :=
    Matrix.of (t.piecewise (1 : Matrix (Fin n) (Fin n) R).row A.row) with hE
  set c : Fin n → Polynomial R :=
    (fun i => if i ∈ t then (Polynomial.X : Polynomial R) else 1) with hc
  have hmap1 : (1 : Matrix (Fin n) (Fin n) R).map Polynomial.C
      = (1 : Matrix (Fin n) (Fin n) (Polynomial R)) := by simp
  have hmat : Matrix.of (t.piecewise ((Polynomial.X : Polynomial R) • (1 : Matrix (Fin n) (Fin n) (Polynomial R)))
          (A.map Polynomial.C))
        = Matrix.of (t.piecewise (fun i => c i • (E.map Polynomial.C i)) (E.map Polynomial.C)) := by
    apply Matrix.ext
    intro i j
    by_cases hi : i ∈ t
    · simp only [Matrix.of_apply, Finset.piecewise, if_pos hi, hE, Matrix.map_apply,
        Matrix.row_apply, Matrix.smul_apply, Pi.smul_apply, smul_eq_mul]
      rw [← hmap1, Matrix.map_apply]
      simp only [hc, if_pos hi]
    · simp only [Matrix.of_apply, Finset.piecewise, if_neg hi, hE, Matrix.map_apply,
        Matrix.row_apply]
  rw [hmat, detExpandXsmulOne_aux_smul c (E.map Polynomial.C) t]
  have hprod : (∏ i ∈ t, c i) = Polynomial.X ^ t.card := by
    have h1 : (∏ i ∈ t, c i) = ∏ _i ∈ t, (Polynomial.X : Polynomial R) :=
      Finset.prod_congr rfl (fun i hi => by simp [hc, hi])
    rw [h1]
    simp [Finset.prod_const]
  have hdet : (E.map Polynomial.C).det = Polynomial.C E.det := by
    simpa using (RingHom.map_det Polynomial.C E).symm
  rw [hprod, hdet]

end Work.TMC14Core
