import Mathlib
import Submission.Work.Drive.BoxParityDefs

namespace Work.Drive

open scoped ContDiff Topology

/-- **The determinant of a matrix of smooth functions is smooth.**

The determinant is a polynomial in the entries, and `Matrix.det_apply'` exhibits it as a finite sum
of products of entries with constant (sign) coefficients. -/
theorem contDiff_det_matrix {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {ι : Type*} [Fintype ι] [DecidableEq ι] {n : WithTop ℕ∞}
    {M : X → Matrix ι ι ℝ} (hM : ∀ i j, ContDiff ℝ n (fun x => M x i j)) :
    ContDiff ℝ n (fun x => (M x).det) := by
  have h : (fun x => (M x).det)
      = fun x => ∑ σ : Equiv.Perm ι,
          (((Equiv.Perm.sign σ : ℤˣ) : ℤ) : ℝ) * ∏ i, M x (σ i) i := by
    funext x
    rw [Matrix.det_apply']
  rw [h]
  exact ContDiff.sum (fun σ _ => contDiff_const.mul (contDiff_prod (fun i _ => hM (σ i) i)))

/-- The cofactor (cross-product) field of a `C^∞` map is `C^∞`.

Each component of `cofactorVec (fderiv ℝ F x)` is the determinant of the `(m × m)`-minor of the
matrix of `fderiv ℝ F x`, hence a polynomial in the partial derivatives of `F`, which are smooth
because `F` is. -/
theorem contDiff_cofactorVectorF {m : ℕ} {F : Work.Drive.Amb m → Work.Drive.Tgt m}
    (hF : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) F) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Work.Drive.cofactorVectorF F) := by
  have hFd : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fderiv ℝ F) := hF.fderiv_right (by simp)
  -- Each maximal minor of the matrix of `fderiv ℝ F` is a smooth function of `x`.
  have hdet : ∀ j : Fin (m + 1), ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun x => ((cofactorMatrix (fderiv ℝ F x)).submatrix (Fin.succAbove j) id).det) := by
    intro j
    apply contDiff_det_matrix
    intro a b
    simp only [Matrix.submatrix_apply, cofactorMatrix]
    fun_prop
  -- Unfold `cofactorVectorF` into its components and reassemble the `EuclideanSpace` structure.
  have hfun : cofactorVectorF F = fun x => WithLp.toLp 2 (fun j : Fin (m + 1) =>
      (-1 : ℝ) ^ (j : ℕ) *
        ((cofactorMatrix (fderiv ℝ F x)).submatrix (Fin.succAbove j) id).det) :=
    funext (fun _ => rfl)
  rw [hfun]
  have hinner : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x : Amb m => fun j : Fin (m + 1) =>
      (-1 : ℝ) ^ (j : ℕ) *
        ((cofactorMatrix (fderiv ℝ F x)).submatrix (Fin.succAbove j) id).det) :=
    (contDiff_pi).2 (fun j => contDiff_const.mul (hdet j))
  exact (PiLp.contDiff_toLp (p := 2) (n := ((⊤ : ℕ∞) : WithTop ℕ∞))).comp hinner

end Work.Drive
