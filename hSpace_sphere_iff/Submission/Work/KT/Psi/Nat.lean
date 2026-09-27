import Mathlib
import Submission.Work.KT.Defs
import Submission.Work.KT.Psi.Basic

/-!
# Naturality of `sq2Part`, `cubePart` under `ℂ`-algebra maps
-/

namespace Work.KT

open Matrix

noncomputable section

variable {A B : Type} [Ring A] [Algebra ℂ A] [Ring B] [Algebra ℂ B]

theorem permMatrix_map (φ : A →ₐ[ℂ] B) {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    (Equiv.Perm.permMatrix A σ).map φ.toRingHom = Equiv.Perm.permMatrix B σ := by
  ext i j
  simp only [Matrix.map_apply, permMatrix_apply']
  by_cases h : σ i = j
  · rw [if_pos h, if_pos h]; exact map_one _
  · rw [if_neg h, if_neg h]; exact map_zero _

theorem matrix_one_map (φ : A →ₐ[ℂ] B) {n : ℕ} :
    (1 : Matrix (Fin n) (Fin n) A).map φ.toRingHom = 1 := by
  ext i j
  simp only [Matrix.map_apply, Matrix.one_apply]
  by_cases h : i = j
  · rw [if_pos h, if_pos h]; exact map_one _
  · rw [if_neg h, if_neg h]; exact map_zero _

theorem map_smul_alg (φ : A →ₐ[ℂ] B) (c : ℂ) {m n : Type} (X : Matrix m n A) :
    (algebraMap ℂ A c • X).map φ.toRingHom = algebraMap ℂ B c • X.map φ.toRingHom := by
  have hc : φ.toRingHom (algebraMap ℂ A c) = algebraMap ℂ B c := by
    simpa using AlgHom.commutes φ c
  ext i j
  simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul]
  rw [map_mul φ.toRingHom (algebraMap ℂ A c) (X i j), hc]

theorem map_mul_alg (φ : A →ₐ[ℂ] B) {m : Type} [Fintype m] (X Y : Matrix m m A) :
    (X * Y).map φ.toRingHom = X.map φ.toRingHom * Y.map φ.toRingHom := Matrix.map_mul

theorem map_add_alg (φ : A →ₐ[ℂ] B) {m n : Type} (X Y : Matrix m n A) :
    (X + Y).map φ.toRingHom = X.map φ.toRingHom + Y.map φ.toRingHom := by
  ext i j
  simp only [Matrix.map_apply, Matrix.add_apply, map_add]

theorem kronMat_map (φ : A →ₐ[ℂ] B) {m m' : ℕ} (M : Matrix (Fin m) (Fin m) A)
    (P : Matrix (Fin m') (Fin m') A) :
    (kronMat M P).map φ.toRingHom = kronMat (M.map φ.toRingHom) (P.map φ.toRingHom) := by
  ext i j
  simp only [kronMat, Matrix.map_apply, Matrix.reindex_apply, Matrix.submatrix_apply,
    Matrix.kroneckerMap_apply, map_mul]


theorem sq2Part_map (φ : A →ₐ[ℂ] B) (ε : ℂ) (p : Mat A) :
    (sq2Part ε p).map φ.toRingHom = sq2Part ε (p.map φ.toRingHom) := by
  unfold sq2Part Mat.map
  simp only
  congr 1
  rw [map_mul_alg, kronMat_map, map_smul_alg, map_add_alg, matrix_one_map, map_smul_alg,
    permMatrix_map]

theorem cubePart_map (φ : A →ₐ[ℂ] B) (lam : ℂ) (p : Mat A) :
    (cubePart lam p).map φ.toRingHom = cubePart lam (p.map φ.toRingHom) := by
  unfold cubePart Mat.map
  simp only
  congr 1
  simp only [map_mul_alg, kronMat_map, map_smul_alg, map_add_alg, matrix_one_map,
    permMatrix_map]

end

end Work.KT
