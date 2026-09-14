import Mathlib
import Submission.Subspace.ApproxSpace
import Submission.Subspace.NumberField
import Submission.Commons.Data.IntVec.primitive_factor
import Submission.Commons.Analysis.Normed.intVec_norm_ge_one
import Submission.Commons.NumberTheory.Height.NumberField.mulHeight_sum_mul_int_le_of_nonempty
import Submission.Commons.NumberTheory.Height.NumberField.one_le_mulHeight_sq_mul_abv
import Submission.Commons.NumberTheory.Height.Vector.pair_ratio_logHeight_ge
import Submission.Commons.NumberTheory.Height.Vector.mulHeight_intVec_ne_zero
import Submission.Commons.LinearAlgebra.Matrix.starVec_ne_zero_iff
import Submission.Commons.LinearAlgebra.Matrix.starVec_dotProduct_eq_zero
import Submission.Commons.LinearAlgebra.Matrix.norm_det_le_prod
import Submission.Commons.LinearAlgebra.Matrix.sum_mul_adjugate_eq
import Submission.Commons.LinearAlgebra.Matrix.det_succAbove_mul_eq_sum_adjugate
import Submission.Commons.LinearAlgebra.LinearForm.exists_smul_of_forall_sum_eq_zero_iff

set_option autoImplicit false
set_option maxHeartbeats 1600000

set_option maxHeartbeats 1600000

open scoped BigOperators Matrix

namespace Submission.Subspace

/-- The cofactor ("star") vector of an `(n+1) × n` matrix over `ℤ`. -/
def starVecZ {n : ℕ} (G : Matrix (Fin (n + 1)) (Fin n) ℤ) : Fin (n + 1) → ℤ :=
  fun i => (-1 : ℤ) ^ (i : ℕ) * (G.submatrix (Fin.succAbove i) id).det

lemma starVecZ_cast {n : ℕ} {R : Type*} [CommRing R] (G : Matrix (Fin (n + 1)) (Fin n) ℤ)
    (i : Fin (n + 1)) :
    ((starVecZ G i : ℤ) : R) = (-1 : R) ^ (i : ℕ) *
      ((G.map (fun x : ℤ => (x : R))).submatrix (Fin.succAbove i) id).det := by
  have h : (((G.submatrix (Fin.succAbove i) id).det : ℤ) : R)
      = ((G.map (fun x : ℤ => (x : R))).submatrix (Fin.succAbove i) id).det := by
    have h0 := RingHom.map_det (Int.castRingHom R) (G.submatrix (Fin.succAbove i) id)
    rw [RingHom.mapMatrix_apply, ← Matrix.submatrix_map, Int.coe_castRingHom] at h0
    exact h0
  rw [starVecZ]
  simp only [Int.cast_mul, Int.cast_pow, Int.cast_neg, Int.cast_one]
  rw [h]

lemma starVecZ_dotProduct {n : ℕ} (G : Matrix (Fin (n + 1)) (Fin n) ℤ) (j : Fin n) :
    ∑ i : Fin (n + 1), (starVecZ G i : ℚ) * ((G i j : ℤ) : ℚ) = 0 := by
  have h := Commons.LinearAlgebra.Matrix.starVec_dotProduct_eq_zero
    (G.map (fun x : ℤ => (x : ℚ))) j
  simpa only [Matrix.map_apply, ← starVecZ_cast (R := ℚ) G] using h

lemma starVecZ_ne_zero {n : ℕ} (G : Matrix (Fin (n + 1)) (Fin n) ℤ)
    (hli : LinearIndependent ℚ (fun j : Fin n => fun i : Fin (n+1) => ((G i j : ℤ) : ℚ))) :
    starVecZ G ≠ 0 := by
  intro h
  have h' : (fun i : Fin (n + 1) => (-1 : ℚ) ^ (i : ℕ) *
      ((G.map (fun x : ℤ => (x : ℚ))).submatrix (Fin.succAbove i) id).det) = 0 := by
    funext i
    have hthis : starVecZ G i = 0 := congrFun h i
    rw [← starVecZ_cast (R := ℚ) G i, hthis]
    simp
  exact (Commons.LinearAlgebra.Matrix.starVec_ne_zero_iff (G.map (fun x : ℤ => (x : ℚ)))).mpr hli h'

/-- The `ℚ`-valued linear form `y ↦ ∑ j, c j * y j`. -/
noncomputable def dotLin {n : ℕ} (c : Fin (n+1) → ℚ) : (Fin (n+1) → ℚ) →ₗ[ℚ] ℚ where
  toFun y := ∑ j, c j * y j
  map_add' y z := by simp [mul_add, Finset.sum_add_distrib]
  map_smul' r y := by simp [Finset.mul_sum, mul_left_comm]

@[simp] lemma dotLin_apply {n : ℕ} (c y : Fin (n+1) → ℚ) : dotLin c y = ∑ j, c j * y j := rfl

lemma dotLin_ne_zero {n : ℕ} {c : Fin (n+1) → ℚ} (hc : c ≠ 0) : dotLin c ≠ 0 := by
  intro h
  apply hc
  funext j
  have h1 : dotLin c (Pi.single j 1) = 0 := by rw [h]; rfl
  simpa [Pi.single_apply] using h1

end Submission.Subspace

namespace Submission.Subspace

lemma neg_one_pow_mul_self {R : Type*} [Ring R] (j : ℕ) : (-1 : R) ^ j * (-1 : R) ^ j = 1 := by
  rw [← pow_add, show j + j = 2 * j from by ring, pow_mul]
  norm_num

end Submission.Subspace
