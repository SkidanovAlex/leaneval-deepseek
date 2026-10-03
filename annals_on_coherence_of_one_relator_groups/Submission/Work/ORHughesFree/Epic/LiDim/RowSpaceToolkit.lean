/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The row-space toolkit for the Sylvester module rank function

This file collects the small facts about the row map `v ↦ v ᵥ* M` of a matrix `M` over a ring `R`
that are used in the proof that the dimension `m - rk(A)` attached to a Sylvester matrix rank
function `rk` is independent of the chosen presentation of a finitely presented module
(Malcolmson's theorem).

They are copied from `Submission/Work/ORHughesFree/Epic/fpDim_eq_of_presentation.lean`, which
cannot be imported here because it (transitively) imports a file that is still being developed.

* `rowMulLin M` is the `R`-linear map `R^a → R^b` of right multiplication by an `a × b` matrix;
* `matOf f` is the matrix of a linear map `R^a → R^b`;
* `matOf_rowMulLin`/`rowMulLin_matOf` say that these two constructions are mutually inverse;
* `exists_eq_mul_of_range_le`: a linear map with range contained in the row space of `M` is right
  multiplication by `M` preceded by a matrix;
* `rk_eq_of_range_eq`: the Sylvester rank of a matrix depends only on its row space.
-/
import Mathlib
import Submission.Work.ORHughesFree.SylvesterRank
import Submission.Work.ORHughesFree.Epic.DimTheory

set_option autoImplicit false

namespace Work.ORHughesFree.Epic.LiDim

open Matrix

variable {R : Type*} [Ring R]

theorem rowMulLin_single {a b : ℕ} (M : Matrix (Fin a) (Fin b) R) (i : Fin a) :
    Work.ORHughesFree.Epic.rowMulLin M (Pi.single i 1) = M i := by
  ext j
  show (∑ l, (Pi.single i (1 : R) : Fin a → R) l * M l j) = M i j
  rw [Finset.sum_eq_single i]
  · simp
  · intro b _ hb
    rw [Pi.single_apply, if_neg hb, zero_mul]
  · intro h; exact absurd (Finset.mem_univ i) h

theorem rowMulLin_mul {a b c : ℕ} (M : Matrix (Fin a) (Fin b) R) (N : Matrix (Fin b) (Fin c) R) :
    Work.ORHughesFree.Epic.rowMulLin (M * N) =
      (Work.ORHughesFree.Epic.rowMulLin N).comp (Work.ORHughesFree.Epic.rowMulLin M) := by
  refine LinearMap.ext fun v => ?_
  refine funext fun j => ?_
  show (∑ i, v i * (∑ k, M i k * N k j)) = ∑ k, (∑ i, v i * M i k) * N k j
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.sum_mul]
  exact Finset.sum_congr rfl fun i _ => by rw [mul_assoc]

/-- The expansion of a vector in the standard basis. -/
theorem eq_sum_smul_single {a : ℕ} (v : Fin a → R) :
    v = ∑ i, v i • (Pi.single i (1 : R) : Fin a → R) := by
  ext j
  rw [Finset.sum_apply]
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [Finset.sum_eq_single j]
  · simp
  · intro b _ hb
    rw [Pi.single_apply, if_neg (Ne.symm hb), mul_zero]
  · intro h; exact absurd (Finset.mem_univ j) h

/-- The matrix of a linear map `(Fin a → R) →ₗ (Fin b → R)`: its `i`-th row is the image of
the `i`-th standard basis vector. -/
noncomputable def matOf {a b : ℕ} (f : (Fin a → R) →ₗ[R] (Fin b → R)) :
    Matrix (Fin a) (Fin b) R :=
  fun i j => f (Pi.single i 1) j

theorem rowMulLin_matOf {a b : ℕ} (f : (Fin a → R) →ₗ[R] (Fin b → R)) :
    Work.ORHughesFree.Epic.rowMulLin (matOf f) = f := by
  refine LinearMap.ext fun v => ?_
  refine funext fun j => ?_
  show (∑ i, v i * f (Pi.single i (1 : R)) j) = f v j
  conv_rhs => rw [eq_sum_smul_single v]
  rw [map_sum]
  simp only [map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]

theorem matOf_rowMulLin {a b : ℕ} (M : Matrix (Fin a) (Fin b) R) :
    matOf (Work.ORHughesFree.Epic.rowMulLin M) = M := by
  ext i j
  simp only [matOf]
  rw [rowMulLin_single]

theorem matOf_comp {a b c : ℕ} (f : (Fin b → R) →ₗ[R] (Fin c → R))
    (g : (Fin a → R) →ₗ[R] (Fin b → R)) :
    matOf (f.comp g) = matOf g * matOf f := by
  have h := rowMulLin_mul (M := matOf g) (N := matOf f)
  rw [rowMulLin_matOf, rowMulLin_matOf] at h
  rw [← h, matOf_rowMulLin]

theorem matOf_sub {a b : ℕ} (f g : (Fin a → R) →ₗ[R] (Fin b → R)) :
    matOf (f - g) = matOf f - matOf g := by
  ext i j
  simp [matOf, LinearMap.sub_apply, Matrix.sub_apply]

theorem matOf_add {a b : ℕ} (f g : (Fin a → R) →ₗ[R] (Fin b → R)) :
    matOf (f + g) = matOf f + matOf g := by
  ext i j
  simp [matOf, LinearMap.add_apply, Matrix.add_apply]

theorem matOf_id (b : ℕ) :
    matOf (LinearMap.id : (Fin b → R) →ₗ[R] (Fin b → R)) = 1 := by
  ext i j
  simp [matOf, Matrix.one_apply, Pi.single_apply, eq_comm]

/-- If the range of `f` is contained in the range of `rowMulLin M`, then `f` is given by right
multiplication by `M` composed with a matrix. -/
theorem exists_eq_mul_of_range_le {a b c : ℕ} (f : (Fin a → R) →ₗ[R] (Fin c → R))
    (M : Matrix (Fin b) (Fin c) R)
    (h : LinearMap.range f ≤ LinearMap.range (Work.ORHughesFree.Epic.rowMulLin M)) :
    ∃ Z : Matrix (Fin a) (Fin b) R, matOf f = Z * M := by
  have hz : ∀ i : Fin a, ∃ z : Fin b → R, Work.ORHughesFree.Epic.rowMulLin M z =
      f (Pi.single i 1) := fun i =>
    LinearMap.mem_range.mp (h (LinearMap.mem_range.mpr ⟨Pi.single i 1, rfl⟩))
  choose z hz' using hz
  refine ⟨fun i => z i, ?_⟩
  ext i j
  simp only [matOf]
  rw [← congrFun (hz' i) j]
  rfl

/-- The Sylvester rank of a matrix depends only on its row space. -/
theorem rk_eq_of_range_eq {a b c : ℕ} (rk : Work.ORHughesFree.SylvesterRank R)
    (A : Matrix (Fin a) (Fin c) R) (B : Matrix (Fin b) (Fin c) R)
    (h : LinearMap.range (Work.ORHughesFree.Epic.rowMulLin A) =
      LinearMap.range (Work.ORHughesFree.Epic.rowMulLin B)) :
    rk.rk a c A = rk.rk b c B := by
  refine le_antisymm ?_ ?_
  · obtain ⟨Z, hZ⟩ := exists_eq_mul_of_range_le (Work.ORHughesFree.Epic.rowMulLin A) B h.le
    have hA : A = Z * B := by rw [← hZ, matOf_rowMulLin]
    rw [hA]
    exact rk.rk_mul_le_right Z B
  · obtain ⟨Z, hZ⟩ := exists_eq_mul_of_range_le (Work.ORHughesFree.Epic.rowMulLin B) A h.ge
    have hB : B = Z * A := by rw [← hZ, matOf_rowMulLin]
    rw [hB]
    exact rk.rk_mul_le_right Z A

end Work.ORHughesFree.Epic.LiDim
