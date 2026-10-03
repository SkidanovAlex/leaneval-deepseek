import Mathlib
import Submission.Work.ORHughesFree.LacNatExt.PolyTDefs

namespace Work.ORHughesFree.NaturalExtension

open Matrix

theorem lacCmat_mul_Cmat {R : Type*} [Ring R] [MulSemiringAction (Multiplicative ℤ) R] (d n : ℕ) :
    lacCmat (R := R) d n * lacCmat (R := R) d n = 1 := by
  have hWBC : lacWBC (R := R) d n = -1 := by
    ext q q'
    rw [lacWBC, Matrix.neg_apply, Matrix.one_apply]
    have hqq : q = q' ↔ ((q.divNat : ℕ) = (q'.divNat : ℕ) ∧ q.modNat = q'.modNat) := by
      constructor
      · rintro rfl; exact ⟨rfl, rfl⟩
      · rintro ⟨h1, h2⟩
        apply finProdFinEquiv.symm.injective
        rw [finProdFinEquiv_symm_apply, finProdFinEquiv_symm_apply, Fin.ext h1, h2]
    by_cases h : q = q'
    · subst h; simp
    · have h1 : ¬ ((q.divNat : ℕ) = (q'.divNat : ℕ) ∧ q.modNat = q'.modNat) :=
        fun hc => h (hqq.mpr hc)
      by_cases ha : (q.divNat : ℕ) = (q'.divNat : ℕ)
      · have hb : ¬ (q.modNat = q'.modNat) := fun hb => h1 ⟨ha, hb⟩
        rw [if_pos ha, if_neg hb, if_neg h]
        simp
      · rw [if_neg ha, if_neg h]
        simp
  have hblock : Matrix.fromBlocks (1 : Matrix (Fin n) (Fin n) R) 0 0
      (-1 : Matrix (Fin (d*n)) (Fin (d*n)) R) =
      Matrix.diagonal (Sum.elim (fun _ : Fin n => (1:R)) (fun _ : Fin (d*n) => (-1:R))) := by
    have h1 : (1 : Matrix (Fin n) (Fin n) R) = Matrix.diagonal (fun _ => (1:R)) :=
      Matrix.diagonal_one.symm
    have h2 : (-1 : Matrix (Fin (d*n)) (Fin (d*n)) R) = Matrix.diagonal (fun _ => (-1:R)) := by
      rw [← Matrix.diagonal_one (n := Fin (d*n)), Matrix.diagonal_neg]
    rw [h1, h2, Matrix.fromBlocks_diagonal]
  have hC : lacCmat (R := R) d n =
      (Matrix.diagonal (Sum.elim (fun _ : Fin n => (1:R))
        (fun _ : Fin (d*n) => (-1:R)))).submatrix finSumFinEquiv.symm finSumFinEquiv.symm := by
    unfold lacCmat
    rw [hWBC, hblock]
  have hg : ∀ x : Fin n ⊕ Fin (d*n),
      Sum.elim (fun _ : Fin n => (1:R)) (fun _ : Fin (d*n) => (-1:R)) x *
      Sum.elim (fun _ : Fin n => (1:R)) (fun _ : Fin (d*n) => (-1:R)) x = 1 := by
    rintro (p | q) <;> simp
  rw [hC, Matrix.submatrix_diagonal _ _ finSumFinEquiv.symm.injective, Matrix.diagonal_mul_diagonal,
    ← Matrix.diagonal_one]
  congr 1
  funext i
  exact hg _

end Work.ORHughesFree.NaturalExtension
