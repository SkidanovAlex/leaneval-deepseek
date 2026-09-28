import Mathlib
import Submission.Work.HP.Defs

/-!
# Gram matrices of bases of integral lattices

For a `ℤ`-basis `b` of a submodule `L ⊆ ℤ^ι`, `gramMat k L b` is the Gram matrix of the
real vectors underlying `b`.  Its determinant is the squared covolume of `L` inside its
real span, so by definition of `detL` we have
`detL L = √(det (gramMat _ L (basisOfPid basis of L)))`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

open MvPolynomial Finset

namespace Work.HP

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The Gram matrix (over `ℝ`) of the real vectors underlying a `ℤ`-basis `b` of a lattice `L`.
Its `(i,j)` entry is the Euclidean inner product of `b i` and `b j`. -/
def gramMat (k : ℕ) (L : Submodule ℤ (ι → ℤ)) (b : Module.Basis (Fin k) ℤ L) :
    Matrix (Fin k) (Fin k) ℝ :=
  Matrix.of fun i j => ∑ x, (((b i : ι → ℤ) x : ℝ) * ((b j : ι → ℤ) x : ℝ))

/-- The real coordinate matrix of a basis. -/
def coordMat (k : ℕ) (L : Submodule ℤ (ι → ℤ)) (b : Module.Basis (Fin k) ℤ L) :
    Matrix (Fin k) ι ℝ :=
  Matrix.of fun i x => ((b i : ι → ℤ) x : ℝ)

/-- `gramMat` is the coordinate matrix times its transpose. -/
lemma gramMat_eq_mul_transpose (k : ℕ) (L : Submodule ℤ (ι → ℤ))
    (b : Module.Basis (Fin k) ℤ L) :
    gramMat k L b = coordMat k L b * (coordMat k L b).transpose := by
  ext i j
  simp [gramMat, coordMat, Matrix.mul_apply]

/-- The determinant of a Gram matrix is nonnegative. -/
lemma gramMat_det_nonneg (k : ℕ) (L : Submodule ℤ (ι → ℤ)) (b : Module.Basis (Fin k) ℤ L) :
    0 ≤ (gramMat k L b).det := by
  rw [gramMat_eq_mul_transpose]
  rw [show coordMat k L b * (coordMat k L b).transpose
      = (Matrix.conjTranspose ((coordMat k L b).transpose)) * (coordMat k L b).transpose by
    ext i j; simp [Matrix.mul_apply]]
  exact Matrix.PosSemidef.det_nonneg (Matrix.posSemidef_conjTranspose_mul_self _)

/-- The defining unfolding of `detL`: it is the square root of the determinant of the Gram
matrix of the basis produced by `Submodule.basisOfPid`. -/
lemma detL_eq_sqrt_gramMat (L : Submodule ℤ (ι → ℤ)) :
    detL L = Real.sqrt (gramMat ((Submodule.basisOfPid (Pi.basisFun ℤ ι) L).1) L
      (Submodule.basisOfPid (Pi.basisFun ℤ ι) L).2).det := by
  rw [detL]
  rfl

/-- `detL` is nonnegative. -/
theorem detL_nonneg_gram (L : Submodule ℤ (ι → ℤ)) : 0 ≤ detL L := by
  rw [detL_eq_sqrt_gramMat]
  exact Real.sqrt_nonneg _

end Work.HP
