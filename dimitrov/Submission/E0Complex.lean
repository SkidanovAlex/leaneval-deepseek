import Mathlib
import Submission.Kronecker

/-!
# E0 over ℂ: the moment/Hankel identity with complex moment pairings

`Submission.PolyaCore.hankelDet_eq_det_momentMatrix` proves that for *monic*
polynomials `pᵢ` of degree `i` the integer Hankel determinant equals the
determinant of the moment matrix `M_{ij} = ∑_{r,s<k} pᵢ.coeff s · pⱼ.coeff r ·
a(s+r)`.  The Pólya/Hankel shell (E2c) works with *complex* moment pairings
(contour integrals), so this module restates that identity with values in
`ℂ`:

    cHankelDet a k = det (cMomentMatrix k a p)   (a : ℕ → ℂ)

for any monic `pᵢ ∈ ℂ[X]` of degree `i`, and records the embedding of the
integer Hankel determinant:

    (hankelDet a k : ℂ) = cHankelDet (fun n => (a n : ℂ)) k .

No sorries may remain in this file.
-/

noncomputable section

open scoped Polynomial

namespace Submission.E0Complex

open Polynomial
open Submission.Kronecker

/-- The `k×k` Hankel matrix `(a(i+j))_{i,j<k}` with complex entries. -/
def cHankelMat (a : ℕ → ℂ) (k : ℕ) : Matrix (Fin k) (Fin k) ℂ :=
  fun i j => a (i.val + j.val)

/-- The Hankel determinant with complex entries. -/
def cHankelDet (a : ℕ → ℂ) (k : ℕ) : ℂ :=
  (cHankelMat a k).det

/-- The `k×k` matrix of moment pairings
`M_{ij} := ∑_{r<k} (∑_{s<k} (pᵢ).coeff s · a (s+r)) · (pⱼ).coeff r`
over `ℂ` (the contracted form of `∑_{r,s} pᵢ.coeff s · pⱼ.coeff r · a(s+r)`). -/
def cMomentMatrix (k : ℕ) (a : ℕ → ℂ) (p : Fin k → ℂ[X]) :
    Matrix (Fin k) (Fin k) ℂ :=
  fun i j =>
    ∑ r : Fin k, (∑ s : Fin k, (p i).coeff s.val * a (s.val + r.val)) * (p j).coeff r.val

/-- Change of basis: `(r,i)`-entry `(p i).coeff r`. -/
def cBasisMatrix (k : ℕ) (p : Fin k → ℂ[X]) : Matrix (Fin k) (Fin k) ℂ :=
  fun r i => (p i).coeff r.val

/-- The moment matrix factorizes as `Cᵀ H C` (definitional after unfolding). -/
lemma cMomentMatrix_eq_basis_mul_hankel (k : ℕ) (a : ℕ → ℂ) (p : Fin k → ℂ[X]) :
    cMomentMatrix k a p =
      Matrix.transpose (cBasisMatrix k p) * cHankelMat a k * cBasisMatrix k p := by
  classical
  ext i j
  simp [cMomentMatrix, cBasisMatrix, cHankelMat, Matrix.mul_apply, Matrix.transpose_apply]

/-- **E0 over ℂ.**  For monic `pᵢ` of degree `i`, the determinant of the
complex moment matrix equals the complex Hankel determinant of `a`. -/
theorem cHankelDet_eq_det_cMomentMatrix (k : ℕ) (a : ℕ → ℂ) (p : Fin k → ℂ[X])
    (hmonic : ∀ i : Fin k, (p i).Monic) (hdeg : ∀ i : Fin k, (p i).natDegree = i.val) :
    cHankelDet a k = (cMomentMatrix k a p).det := by
  classical
  have hMom : cMomentMatrix k a p =
      Matrix.transpose (cBasisMatrix k p) * cHankelMat a k * cBasisMatrix k p :=
    cMomentMatrix_eq_basis_mul_hankel k a p
  have hdetC : (cBasisMatrix k p).det = 1 := by
    have hb : cBasisMatrix k p =
        Matrix.of (fun i j : Fin k => (p j).coeff i.val) := by
      ext i j
      rfl
    rw [hb]
    exact Matrix.det_matrixOfPolynomials (n := k) p (fun i => hdeg i) (fun i => hmonic i)
  rw [hMom]
  have hdetprod : ((Matrix.transpose (cBasisMatrix k p)) * cHankelMat a k * cBasisMatrix k p).det
      = (cHankelMat a k).det := by
    calc
      ((Matrix.transpose (cBasisMatrix k p)) * cHankelMat a k * cBasisMatrix k p).det
          = ((Matrix.transpose (cBasisMatrix k p)) * cHankelMat a k).det *
              (cBasisMatrix k p).det := Matrix.det_mul _ _
      _ = (Matrix.transpose (cBasisMatrix k p)).det * (cHankelMat a k).det *
              (cBasisMatrix k p).det := by rw [Matrix.det_mul]
      _ = (cHankelMat a k).det := by
            rw [Matrix.det_transpose, hdetC]
            norm_num
  rw [hdetprod]
  rfl

/-- The integer Hankel determinant embeds into the complex one. -/
lemma hankelDet_cast_complex (a : ℕ → ℤ) (k : ℕ) :
    (hankelDet a k : ℂ) = cHankelDet (fun n : ℕ => (a n : ℂ)) k := by
  have hmat : cHankelMat (fun n : ℕ => (a n : ℂ)) k =
      (Int.castRingHom ℂ).mapMatrix (hankelMat a k) := by
    ext i j
    simp [cHankelMat, hankelMat]
  have h : cHankelDet (fun n : ℕ => (a n : ℂ)) k = (hankelDet a k : ℂ) := by
    calc
      cHankelDet (fun n : ℕ => (a n : ℂ)) k = (cHankelMat (fun n : ℕ => (a n : ℂ)) k).det := rfl
      _ = ((Int.castRingHom ℂ).mapMatrix (hankelMat a k)).det := by rw [hmat]
      _ = (Int.castRingHom ℂ) ((hankelMat a k).det) :=
            (RingHom.map_det (Int.castRingHom ℂ) (hankelMat a k)).symm
      _ = (hankelDet a k : ℂ) := by
        rw [show (hankelMat a k).det = hankelDet a k by
          unfold hankelDet hankelMat
          rfl]
        rfl
  exact h.symm

end Submission.E0Complex

end
