/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: hSpace_sphere_iff team

# Auxiliary matrix bookkeeping for `Work.KT.D2.stab_loop_nullhomotopic`

Conjugation by an invertible matrix, reindexing of matrices along an equivalence of index types,
and the block decomposition of a matrix commuting with the standard idempotent `diag(1,0)`.
-/
import Mathlib

namespace Work.KT.D2

open Matrix

noncomputable section

/-! ## Conjugation by a unit -/

lemma units_mul_inv_val {α : Type*} [Monoid α] (u : αˣ) : (↑u : α) * ↑(u⁻¹) = 1 := by
  simpa using congrArg (fun w : αˣ => (↑w : α)) (Units.mul_inv u)

lemma units_inv_mul_val {α : Type*} [Monoid α] (u : αˣ) : (↑(u⁻¹) : α) * ↑u = 1 := by
  simpa using congrArg (fun w : αˣ => (↑w : α)) (Units.inv_mul u)

/-- Conjugation `X ↦ u * X * u⁻¹` by an invertible matrix. -/
abbrev conjUMat {n : ℕ} (u : (Matrix (Fin n) (Fin n) ℂ)ˣ) (X : Matrix (Fin n) (Fin n) ℂ) :
    Matrix (Fin n) (Fin n) ℂ :=
  (↑u : Matrix (Fin n) (Fin n) ℂ) * X * (↑(u⁻¹) : Matrix (Fin n) (Fin n) ℂ)

/-- Conjugation `X ↦ u⁻¹ * X * u` by an invertible matrix. -/
abbrev conjUInv {n : ℕ} (u : (Matrix (Fin n) (Fin n) ℂ)ˣ) (X : Matrix (Fin n) (Fin n) ℂ) :
    Matrix (Fin n) (Fin n) ℂ :=
  (↑(u⁻¹) : Matrix (Fin n) (Fin n) ℂ) * X * (↑u : Matrix (Fin n) (Fin n) ℂ)

lemma conjUMat_one {n : ℕ} (u : (Matrix (Fin n) (Fin n) ℂ)ˣ) :
    conjUMat u (1 : Matrix (Fin n) (Fin n) ℂ) = 1 := by
  unfold conjUMat
  rw [mul_one, units_mul_inv_val]

lemma conjUInv_one {n : ℕ} (u : (Matrix (Fin n) (Fin n) ℂ)ˣ) :
    conjUInv u (1 : Matrix (Fin n) (Fin n) ℂ) = 1 := by
  unfold conjUInv
  rw [mul_one, units_inv_mul_val]

lemma conjUMat_mul {n : ℕ} (u : (Matrix (Fin n) (Fin n) ℂ)ˣ) (X Y : Matrix (Fin n) (Fin n) ℂ) :
    conjUMat u (X * Y) = conjUMat u X * conjUMat u Y := by
  unfold conjUMat
  rw [← mul_assoc (↑u : Matrix (Fin n) (Fin n) ℂ) X Y]
  simp only [mul_assoc]
  rw [← mul_assoc (↑(u⁻¹) : Matrix (Fin n) (Fin n) ℂ) (↑u : Matrix (Fin n) (Fin n) ℂ)
      (Y * (↑(u⁻¹) : Matrix (Fin n) (Fin n) ℂ)), units_inv_mul_val, one_mul]

lemma conjUInv_mul {n : ℕ} (u : (Matrix (Fin n) (Fin n) ℂ)ˣ) (X Y : Matrix (Fin n) (Fin n) ℂ) :
    conjUInv u (X * Y) = conjUInv u X * conjUInv u Y := by
  unfold conjUInv
  rw [← mul_assoc (↑(u⁻¹) : Matrix (Fin n) (Fin n) ℂ) X Y]
  simp only [mul_assoc]
  rw [← mul_assoc (↑u : Matrix (Fin n) (Fin n) ℂ) (↑(u⁻¹) : Matrix (Fin n) (Fin n) ℂ)
      (Y * (↑u : Matrix (Fin n) (Fin n) ℂ)), units_mul_inv_val, one_mul]

/-- Conjugating twice (in the two directions) returns the original matrix. -/
lemma conjUInv_conjUMat {n : ℕ} (u : (Matrix (Fin n) (Fin n) ℂ)ˣ) (X : Matrix (Fin n) (Fin n) ℂ) :
    conjUInv u (conjUMat u X) = X := by
  unfold conjUInv conjUMat
  simp only [mul_assoc]
  rw [units_inv_mul_val, mul_one]
  rw [← mul_assoc (↑(u⁻¹) : Matrix (Fin n) (Fin n) ℂ) (↑u : Matrix (Fin n) (Fin n) ℂ) X,
      units_inv_mul_val, one_mul]

lemma conjUMat_conjUInv {n : ℕ} (u : (Matrix (Fin n) (Fin n) ℂ)ˣ) (X : Matrix (Fin n) (Fin n) ℂ) :
    conjUMat u (conjUInv u X) = X := by
  unfold conjUInv conjUMat
  simp only [mul_assoc]
  rw [units_mul_inv_val, mul_one]
  rw [← mul_assoc (↑u : Matrix (Fin n) (Fin n) ℂ) (↑(u⁻¹) : Matrix (Fin n) (Fin n) ℂ) X,
      units_mul_inv_val, one_mul]

/-! ## Reindexing along an equivalence of index types -/

lemma reindexSymmReindex {k m n : ℕ} (ε : Fin k ⊕ Fin m ≃ Fin n)
    (Y : Matrix (Fin k ⊕ Fin m) (Fin k ⊕ Fin m) ℂ) :
    Matrix.reindex ε.symm ε.symm (Matrix.reindex ε ε Y) = Y := by
  ext i j
  simp [Matrix.reindex_apply, Matrix.submatrix_apply]

lemma reindexReindexSymm {k m n : ℕ} (ε : Fin k ⊕ Fin m ≃ Fin n)
    (X : Matrix (Fin n) (Fin n) ℂ) :
    Matrix.reindex ε ε (Matrix.reindex ε.symm ε.symm X) = X := by
  ext i j
  simp [Matrix.reindex_apply, Matrix.submatrix_apply]

lemma reindexSymm_mul {k m n : ℕ} (ε : Fin k ⊕ Fin m ≃ Fin n)
    (X Y : Matrix (Fin n) (Fin n) ℂ) :
    Matrix.reindex ε.symm ε.symm (X * Y)
      = Matrix.reindex ε.symm ε.symm X * Matrix.reindex ε.symm ε.symm Y := by
  rw [← Matrix.coe_reindexAlgEquiv ℂ ℂ ε.symm]
  exact map_mul _ X Y

lemma reindex_mul {k m n : ℕ} (ε : Fin k ⊕ Fin m ≃ Fin n)
    (X Y : Matrix (Fin k ⊕ Fin m) (Fin k ⊕ Fin m) ℂ) :
    Matrix.reindex ε ε (X * Y) = Matrix.reindex ε ε X * Matrix.reindex ε ε Y := by
  rw [← Matrix.coe_reindexAlgEquiv ℂ ℂ ε]
  exact map_mul _ X Y

lemma reindex_one {k m n : ℕ} (ε : Fin k ⊕ Fin m ≃ Fin n) :
    Matrix.reindex ε ε (1 : Matrix (Fin k ⊕ Fin m) (Fin k ⊕ Fin m) ℂ) = 1 := by
  rw [← Matrix.coe_reindexAlgEquiv ℂ ℂ ε]
  exact map_one _

/-! ## Block matrices -/

/-- A matrix commuting with the standard idempotent `diag(1_k, 0_m)` is block diagonal. -/
lemma eq_fromBlocks_of_comm {k m : ℕ} (Y : Matrix (Fin k ⊕ Fin m) (Fin k ⊕ Fin m) ℂ)
    (h : Y * Matrix.fromBlocks (1 : Matrix (Fin k) (Fin k) ℂ) 0 0 0
      = Matrix.fromBlocks (1 : Matrix (Fin k) (Fin k) ℂ) 0 0 0 * Y) :
    Y = Matrix.fromBlocks (Y.submatrix Sum.inl Sum.inl) 0 0 (Y.submatrix Sum.inr Sum.inr) := by
  have hY : Y = Matrix.fromBlocks (Y.submatrix Sum.inl Sum.inl) (Y.submatrix Sum.inl Sum.inr)
      (Y.submatrix Sum.inr Sum.inl) (Y.submatrix Sum.inr Sum.inr) := by
    ext (i|i) (j|j) <;> rfl
  rw [hY] at h
  rw [Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply] at h
  simp only [Matrix.mul_one, Matrix.mul_zero, add_zero, Matrix.one_mul, Matrix.zero_mul] at h
  have hB : Y.submatrix Sum.inl Sum.inr = 0 := by
    ext i j
    have hh := congrFun (congrFun h (Sum.inl i)) (Sum.inr j)
    simpa using hh.symm
  have hC : Y.submatrix Sum.inr Sum.inl = 0 := by
    ext i j
    have hh := congrFun (congrFun h (Sum.inr i)) (Sum.inl j)
    simpa using hh
  rw [hB, hC] at hY
  exact hY

lemma det_fromBlocks_diag {k m : ℕ} (A : Matrix (Fin k) (Fin k) ℂ) (D : Matrix (Fin m) (Fin m) ℂ) :
    (Matrix.fromBlocks A 0 0 D).det = A.det * D.det :=
  Matrix.det_fromBlocks_zero₂₁ A 0 D

lemma isUnit_fromBlocks_diag {k m : ℕ} (A : Matrix (Fin k) (Fin k) ℂ)
    (D : Matrix (Fin m) (Fin m) ℂ) :
    IsUnit (Matrix.fromBlocks A 0 0 D) ↔ IsUnit A ∧ IsUnit D := by
  rw [Matrix.isUnit_iff_isUnit_det, Matrix.isUnit_iff_isUnit_det, Matrix.isUnit_iff_isUnit_det,
    det_fromBlocks_diag]
  constructor
  · intro h
    exact ⟨isUnit_iff_ne_zero.mpr fun h0 => isUnit_iff_ne_zero.mp h (by rw [h0, zero_mul]),
      isUnit_iff_ne_zero.mpr fun h0 => isUnit_iff_ne_zero.mp h (by rw [h0, mul_zero])⟩
  · rintro ⟨h1, h2⟩
    exact isUnit_iff_ne_zero.mpr
      (mul_ne_zero (isUnit_iff_ne_zero.mp h1) (isUnit_iff_ne_zero.mp h2))


lemma det_units_mul_inv {n : ℕ} (u : (Matrix (Fin n) (Fin n) ℂ)ˣ) :
    (↑u : Matrix (Fin n) (Fin n) ℂ).det * (↑(u⁻¹) : Matrix (Fin n) (Fin n) ℂ).det = 1 := by
  have h := congrArg Matrix.det (units_mul_inv_val u)
  rwa [Matrix.det_mul, Matrix.det_one] at h

lemma det_units_inv_mul {n : ℕ} (u : (Matrix (Fin n) (Fin n) ℂ)ˣ) :
    (↑(u⁻¹) : Matrix (Fin n) (Fin n) ℂ).det * (↑u : Matrix (Fin n) (Fin n) ℂ).det = 1 := by
  have h := congrArg Matrix.det (units_inv_mul_val u)
  rwa [Matrix.det_mul, Matrix.det_one] at h

lemma conjUInv_det {n : ℕ} (u : (Matrix (Fin n) (Fin n) ℂ)ˣ) (A : Matrix (Fin n) (Fin n) ℂ) :
    (conjUInv u A).det = A.det := by
  show ((↑(u⁻¹) : Matrix (Fin n) (Fin n) ℂ) * A * (↑u : Matrix (Fin n) (Fin n) ℂ)).det = A.det
  rw [Matrix.det_mul, Matrix.det_mul, mul_assoc,
    mul_comm A.det (↑u : Matrix (Fin n) (Fin n) ℂ).det, ← mul_assoc, det_units_inv_mul, one_mul]

lemma conjUMat_det {n : ℕ} (u : (Matrix (Fin n) (Fin n) ℂ)ˣ) (A : Matrix (Fin n) (Fin n) ℂ) :
    (conjUMat u A).det = A.det := by
  show ((↑u : Matrix (Fin n) (Fin n) ℂ) * A * (↑(u⁻¹) : Matrix (Fin n) (Fin n) ℂ)).det = A.det
  rw [Matrix.det_mul, Matrix.det_mul, mul_assoc,
    mul_comm A.det (↑(u⁻¹) : Matrix (Fin n) (Fin n) ℂ).det, ← mul_assoc, det_units_mul_inv, one_mul]

lemma conjUInv_add {n : ℕ} (u : (Matrix (Fin n) (Fin n) ℂ)ˣ) (A B : Matrix (Fin n) (Fin n) ℂ) :
    conjUInv u (A + B) = conjUInv u A + conjUInv u B := by
  unfold conjUInv
  rw [mul_add, add_mul]

lemma conjUInv_sub {n : ℕ} (u : (Matrix (Fin n) (Fin n) ℂ)ˣ) (A B : Matrix (Fin n) (Fin n) ℂ) :
    conjUInv u (A - B) = conjUInv u A - conjUInv u B := by
  unfold conjUInv
  rw [mul_sub, sub_mul]

lemma reindex_add {k m n : ℕ} (ε : Fin k ⊕ Fin m ≃ Fin n)
    (X Y : Matrix (Fin k ⊕ Fin m) (Fin k ⊕ Fin m) ℂ) :
    Matrix.reindex ε ε (X + Y) = Matrix.reindex ε ε X + Matrix.reindex ε ε Y := by
  rw [← Matrix.coe_reindexAlgEquiv ℂ ℂ ε]
  exact map_add _ X Y

lemma reindex_sub {k m n : ℕ} (ε : Fin k ⊕ Fin m ≃ Fin n)
    (X Y : Matrix (Fin k ⊕ Fin m) (Fin k ⊕ Fin m) ℂ) :
    Matrix.reindex ε ε (X - Y) = Matrix.reindex ε ε X - Matrix.reindex ε ε Y := by
  rw [← Matrix.coe_reindexAlgEquiv ℂ ℂ ε]
  exact map_sub _ X Y


end

end Work.KT.D2
