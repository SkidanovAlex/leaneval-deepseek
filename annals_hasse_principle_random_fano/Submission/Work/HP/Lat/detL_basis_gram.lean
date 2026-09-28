import Mathlib
import Submission.Work.HP.Defs

/-!
# `detL` is the square root of the determinant of the Gram matrix of *any* basis

`Work.HP.detL` is defined as the square root of the determinant of the Gram matrix of one
particular `ℤ`-basis of `L`, namely the one produced by `Submodule.basisOfPid`.  This file shows
that the choice of basis is immaterial: for every `ℤ`-basis `b` of `L`, the determinant of the Gram
matrix of `b` equals `detL L ^ 2`.

The mathematical content is the classical change-of-basis formula for the Gram matrix:
if `T = b.toMatrix c` is the transition matrix between two bases `b`, `c` of `L`, then
`G_c = Tᵀ G_b T`, and `T` is invertible over `ℤ` with inverse `c.toMatrix b`, so `det T = ±1`
and `det G_c = (det T)^2 det G_b = det G_b`.  The change-of-basis formula itself is an instance of
`LinearMap.BilinForm.toMatrix_mul_basis_toMatrix` for the `ℤ`-bilinear form given by the standard
inner product on `L ⊆ ℤ^ι`.
-/

set_option autoImplicit false

noncomputable section

open Matrix

namespace Work.HP.Lat

/-! ## The auxiliary inner product on `ℤ^ι` and the Gram matrix -/

section defs
variable {ι : Type*} [Fintype ι]

/-- The standard `ℤ`-valued inner product on `ι → ℤ`, written as a partial application. -/
def ip (v w : ι → ℤ) : ℤ := ∑ i, v i * w i

/-- The inner product restricted to an integral lattice `L`, as a `ℤ`-bilinear form. -/
def ipForm (L : Submodule ℤ (ι → ℤ)) : LinearMap.BilinForm ℤ L :=
  LinearMap.mk₂ ℤ (fun x y => ip (x : ι → ℤ) (y : ι → ℤ))
    (fun x y z => by simp [ip, Finset.sum_add_distrib, add_mul])
    (fun c x y => by
      simp only [ip, Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
      exact Finset.sum_congr rfl (fun i _ => by ring))
    (fun x y z => by simp [ip, Finset.sum_add_distrib, mul_add])
    (fun c x y => by
      simp only [ip, Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
      exact Finset.sum_congr rfl (fun i _ => by ring))

/-- The Gram matrix, over `ℝ`, of a `ℤ`-basis `b` of an integral lattice `L`. -/
def gramR {κ : Type*} [Fintype κ] (L : Submodule ℤ (ι → ℤ)) (b : Module.Basis κ ℤ L) :
    Matrix κ κ ℝ :=
  Matrix.of fun i j => ∑ x, (((b i : ι → ℤ) x : ℝ) * ((b j : ι → ℤ) x : ℝ))

end defs

section gram
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
/-- The `ℝ`-Gram matrix of a basis is the `ℝ`-image of the matrix of the `ℤ`-bilinear form `ipForm`
in that basis. -/
lemma gramR_eq_toMatrix (L : Submodule ℤ (ι → ℤ)) {κ : Type*} [Fintype κ] [DecidableEq κ]
    (b : Module.Basis κ ℤ L) :
    gramR L b = (LinearMap.BilinForm.toMatrix b (ipForm L)).map (fun z : ℤ => (z : ℝ)) := by
  ext i j
  simp only [gramR, Matrix.of_apply, Matrix.map_apply, LinearMap.BilinForm.toMatrix_apply,
    LinearMap.mk₂_apply, ipForm, ip, Int.cast_sum, Int.cast_mul]

omit [Fintype ι] [DecidableEq ι] in
/-- The transition matrix between two `ℤ`-bases of the same lattice has determinant a unit of `ℤ`,
hence determinant `±1`; consequently its determinant squares to `1`. -/
lemma det_toMatrix_self_sq {L : Submodule ℤ (ι → ℤ)} {κ : Type*} [Fintype κ] [DecidableEq κ]
    (b c : Module.Basis κ ℤ L) : (b.toMatrix c).det * (b.toMatrix c).det = 1 := by
  have h2 : (b.toMatrix c).det * (c.toMatrix b).det = 1 := by
    rw [← Matrix.det_mul, Module.Basis.toMatrix_mul_toMatrix_flip b c, Matrix.det_one]
  rcases Int.eq_one_or_neg_one_of_mul_eq_one h2 with h | h <;> rw [h] <;> norm_num

omit [DecidableEq ι] in
/-- The Gram determinant of a basis of a lattice is independent of the basis (same index type). -/
lemma det_gramR_eq_same (L : Submodule ℤ (ι → ℤ)) {κ : Type*} [Fintype κ] [DecidableEq κ]
    (b c : Module.Basis κ ℤ L) : (gramR L b).det = (gramR L c).det := by
  have hdet : (LinearMap.BilinForm.toMatrix c (ipForm L)).det
      = (LinearMap.BilinForm.toMatrix b (ipForm L)).det := by
    have hbc := LinearMap.BilinForm.toMatrix_mul_basis_toMatrix b c (ipForm L)
    calc (LinearMap.BilinForm.toMatrix c (ipForm L)).det
        = ((b.toMatrix c)ᵀ * LinearMap.BilinForm.toMatrix b (ipForm L)
            * b.toMatrix c).det := by rw [hbc]
      _ = ((b.toMatrix c).det * (b.toMatrix c).det)
            * (LinearMap.BilinForm.toMatrix b (ipForm L)).det := by
          rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose]; ring
      _ = (LinearMap.BilinForm.toMatrix b (ipForm L)).det := by
          rw [det_toMatrix_self_sq b c, one_mul]
  rw [gramR_eq_toMatrix, gramR_eq_toMatrix, ← Int.cast_det, ← Int.cast_det, hdet]

omit [DecidableEq ι] in
/-- Reindexing a basis permutes the rows and columns of its Gram matrix. -/
lemma gramR_reindex (L : Submodule ℤ (ι → ℤ)) {κ κ' : Type*} [Fintype κ] [Fintype κ']
    (b : Module.Basis κ' ℤ L) (e : κ ≃ κ') :
    gramR L (b.reindex e.symm) = (gramR L b).submatrix e e := by
  ext i j
  simp [gramR, Matrix.submatrix_apply, Module.Basis.reindex_apply]

omit [DecidableEq ι] in
/-- The Gram determinant of a basis of a lattice is independent of the basis, for bases indexed by
arbitrary (finite) index types. -/
lemma det_gramR_eq (L : Submodule ℤ (ι → ℤ)) {κ κ' : Type*} [Fintype κ] [DecidableEq κ]
    [Fintype κ'] [DecidableEq κ'] (b : Module.Basis κ ℤ L) (c : Module.Basis κ' ℤ L) :
    (gramR L b).det = (gramR L c).det := by
  let e : κ ≃ κ' := b.indexEquiv c
  have h1 : (gramR L b).det = (gramR L (c.reindex e.symm)).det :=
    det_gramR_eq_same L b (c.reindex e.symm)
  have h2 : (gramR L (c.reindex e.symm)).det = (gramR L c).det := by
    rw [gramR_reindex L c e, Matrix.det_submatrix_equiv_self]
  rw [h1, h2]

end gram

/-- **`detL` is basis-independent.**  For any `ℤ`-basis `b` of `L ⊆ ℤ^ι`, the determinant of the
covolume form `detL L` equals the square root of the determinant of the Gram matrix of `b`. -/
theorem detL_basis_gram {ι : Type*} [Fintype ι] [DecidableEq ι]
    {κ : Type*} [Fintype κ] [DecidableEq κ] (L : Submodule ℤ (ι → ℤ)) (b : Module.Basis κ ℤ L) :
    detL L = Real.sqrt (Matrix.det (Matrix.of fun i j : κ =>
      ∑ x, (((b i : ι → ℤ) x : ℝ) * ((b j : ι → ℤ) x : ℝ)))) := by
  have h := det_gramR_eq L (Submodule.basisOfPid (Pi.basisFun ℤ ι) L).2 b
  rw [detL]
  exact congrArg Real.sqrt h

end Work.HP.Lat
