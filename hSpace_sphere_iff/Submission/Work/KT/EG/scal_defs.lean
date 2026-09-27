/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: hSpace_sphere_iff team
-/
import Mathlib
import Submission.Work.KT.Fund.Kappa

/-!
# `Work.KT.EG.scal_defs` — the scalar matrix unit `c • 1_m`

For a unit `c` of the circle algebra `C(X × S¹, ℂ)`, `scalUnit X m c` is the unit of
`m × m` matrices over `C(X × S¹, ℂ)` whose underlying matrix is the scalar matrix `c • 1_m`.
It is the ring-homomorphic image of `c` under `Matrix.scalar (Fin m)`; in particular
`scalUnit X 1 (Work.KT.zUnit X)` is `Fund.zUnitMat X`, the Bott generator.
-/

namespace Work.KT.EG

open Matrix

noncomputable section

/-- The scalar matrix unit `c • 1_m`. -/
def scalUnit (X : Type) [TopologicalSpace X] (m : ℕ) (c : (C(X × Sph ℂ, ℂ))ˣ) :
    (Matrix (Fin m) (Fin m) C(X × Sph ℂ, ℂ))ˣ :=
  Units.map (Matrix.scalar (Fin m) : C(X × Sph ℂ, ℂ) →+*
    Matrix (Fin m) (Fin m) C(X × Sph ℂ, ℂ)) c

@[simp] lemma scalUnit_val (X : Type) [TopologicalSpace X] (m : ℕ) (c : (C(X × Sph ℂ, ℂ))ˣ) :
    (scalUnit X m c : Matrix (Fin m) (Fin m) C(X × Sph ℂ, ℂ))
      = (c : C(X × Sph ℂ, ℂ)) • (1 : Matrix (Fin m) (Fin m) C(X × Sph ℂ, ℂ)) := by
  show (Matrix.scalar (Fin m)) (c : C(X × Sph ℂ, ℂ)) = _
  rw [Matrix.scalar_apply, Matrix.smul_one_eq_diagonal]

@[simp] lemma scalUnit_one (X : Type) [TopologicalSpace X] (m : ℕ) :
    scalUnit X m 1 = 1 := map_one _

@[simp] lemma scalUnit_mul (X : Type) [TopologicalSpace X] (m : ℕ)
    (c d : (C(X × Sph ℂ, ℂ))ˣ) :
    scalUnit X m (c * d) = scalUnit X m c * scalUnit X m d := map_mul _ _ _

@[simp] lemma scalUnit_inv (X : Type) [TopologicalSpace X] (m : ℕ) (c : (C(X × Sph ℂ, ℂ))ˣ) :
    scalUnit X m c⁻¹ = (scalUnit X m c)⁻¹ := map_inv _ _

@[simp] lemma scalUnit_pow (X : Type) [TopologicalSpace X] (m : ℕ)
    (c : (C(X × Sph ℂ, ℂ))ˣ) (k : ℕ) :
    scalUnit X m (c ^ k) = (scalUnit X m c) ^ k := map_pow _ _ _

@[simp] lemma scalUnit_zpow (X : Type) [TopologicalSpace X] (m : ℕ)
    (c : (C(X × Sph ℂ, ℂ))ˣ) (k : ℤ) :
    scalUnit X m (c ^ k) = (scalUnit X m c) ^ k := map_zpow _ _ _

/-- The `1 × 1` scalar unit of the coordinate `z` is `Fund.zUnitMat`. -/
lemma scalUnit_zUnit (X : Type) [TopologicalSpace X] :
    scalUnit X 1 (Work.KT.zUnit X) = Work.KT.Fund.zUnitMat X := rfl

/-! ## Two generic matrix identities -/

/-- A scalar matrix times a matrix is the scalar multiple (generic ring version). -/
lemma smul_one_mul_mat {R : Type} [CommRing R] {m : ℕ} (x : R) (M : Matrix (Fin m) (Fin m) R) :
    (x • (1 : Matrix (Fin m) (Fin m) R)) * M = x • M := by
  first
  | rw [Matrix.smul_mul, one_mul]
  | ext i j
    rw [Matrix.smul_one_eq_diagonal, Matrix.diagonal_mul, Matrix.smul_apply]
    simp
  | ext i j
    simp [Matrix.smul_one_eq_diagonal, Matrix.diagonal_mul, Matrix.smul_apply, Matrix.mul_apply,
      Matrix.one_apply]

/-- A matrix times a scalar matrix is the scalar multiple (generic ring version). -/
lemma mul_smul_one_mat {R : Type} [CommRing R] {m : ℕ} (M : Matrix (Fin m) (Fin m) R) (x : R) :
    M * (x • (1 : Matrix (Fin m) (Fin m) R)) = x • M := by
  first
  | rw [Matrix.mul_smul, mul_one]
  | ext i j
    rw [Matrix.smul_one_eq_diagonal, Matrix.mul_diagonal, Matrix.smul_apply]
    simp
  | ext i j
    simp [Matrix.smul_one_eq_diagonal, Matrix.mul_diagonal, Matrix.smul_apply, Matrix.mul_apply,
      Matrix.one_apply]

/-- Block form of the scalar matrix: `c • 1_{m+1}` is the reindexed block matrix with the two
scalar blocks `c • 1_m` and `c • 1_1`. -/
lemma smul_one_succ {R : Type} [CommRing R] {m : ℕ} (x : R) :
    (x • (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) R))
      = Matrix.reindex finSumFinEquiv finSumFinEquiv
          (Matrix.fromBlocks (x • (1 : Matrix (Fin m) (Fin m) R)) 0 0
            (x • (1 : Matrix (Fin 1) (Fin 1) R))) := by
  rw [Matrix.smul_one_eq_diagonal, Matrix.smul_one_eq_diagonal, Matrix.smul_one_eq_diagonal,
    Matrix.fromBlocks_diagonal, Matrix.reindex_apply, Matrix.submatrix_diagonal_equiv]
  rw [show (fun _ : Fin (m + 1) => x)
      = (Sum.elim (fun _ : Fin m => x) (fun _ : Fin 1 => x)) ∘ ⇑(finSumFinEquiv.symm) from by
    funext i
    cases h : finSumFinEquiv.symm i <;> simp [h]]

/-- Block form of the scalar matrix unit at the level of `scalUnit`. -/
lemma scalUnit_succ (X : Type) [TopologicalSpace X] (m : ℕ) (c : (C(X × Sph ℂ, ℂ))ˣ) :
    (scalUnit X (m + 1) c : Matrix (Fin (m + 1)) (Fin (m + 1)) C(X × Sph ℂ, ℂ))
      = Matrix.reindex finSumFinEquiv finSumFinEquiv
          (Matrix.fromBlocks (scalUnit X m c) 0 0 (scalUnit X 1 c)) := by
  first
  | rw [scalUnit_val, scalUnit_val, scalUnit_val]
    exact smul_one_succ (c : C(X × Sph ℂ, ℂ))
  | rw [scalUnit_val, scalUnit_val, scalUnit_val]
    simpa using smul_one_succ (c : C(X × Sph ℂ, ℂ))

/-- A scalar matrix unit times a matrix unit is the scalar multiple. -/
lemma scalUnit_mul_val (X : Type) [TopologicalSpace X] (m : ℕ) (c : (C(X × Sph ℂ, ℂ))ˣ)
    (W : (Matrix (Fin m) (Fin m) C(X × Sph ℂ, ℂ))ˣ) :
    ((scalUnit X m c * W : (Matrix (Fin m) (Fin m) C(X × Sph ℂ, ℂ))ˣ) :
        Matrix (Fin m) (Fin m) C(X × Sph ℂ, ℂ))
      = (c : C(X × Sph ℂ, ℂ)) • (W : Matrix (Fin m) (Fin m) C(X × Sph ℂ, ℂ)) := by
  first
  | rw [Units.val_mul, scalUnit_val]
    exact smul_one_mul_mat (c : C(X × Sph ℂ, ℂ)) (W : Matrix (Fin m) (Fin m) C(X × Sph ℂ, ℂ))
  | rw [Units.val_mul, scalUnit_val, Matrix.scalar_apply]
    exact smul_one_mul_mat (c : C(X × Sph ℂ, ℂ)) (W : Matrix (Fin m) (Fin m) C(X × Sph ℂ, ℂ))

/-- Matrix units commute with scalar matrix units. -/
lemma scalUnit_comm (X : Type) [TopologicalSpace X] (m : ℕ) (c : (C(X × Sph ℂ, ℂ))ˣ)
    (W : (Matrix (Fin m) (Fin m) C(X × Sph ℂ, ℂ))ˣ) :
    (scalUnit X m c : Matrix (Fin m) (Fin m) C(X × Sph ℂ, ℂ))
        * (W : Matrix (Fin m) (Fin m) C(X × Sph ℂ, ℂ))
      = (W : Matrix (Fin m) (Fin m) C(X × Sph ℂ, ℂ))
        * (scalUnit X m c : Matrix (Fin m) (Fin m) C(X × Sph ℂ, ℂ)) := by
  first
  | rw [scalUnit_val, smul_one_mul_mat, mul_smul_one_mat]
  | rw [scalUnit_val, smul_one_mul_mat]
    exact (mul_smul_one_mat (W : Matrix (Fin m) (Fin m) C(X × Sph ℂ, ℂ))
      (c : C(X × Sph ℂ, ℂ))).symm

end

end Work.KT.EG
