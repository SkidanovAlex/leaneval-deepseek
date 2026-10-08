/-
The Frobenius conjugate-transpose `Aᴴ` and the special unitary group `SU(3, 2^n)`.

We realise `herm` as the entrywise transpose followed by the `(2^n)`-Frobenius automorphism
`frob n : x ↦ x ^ (2^n)` of `GF(2^(2n))`.  Since `frob n` is an involution of `GF(2^(2n))`
(the `n`-fold Frobenius has order `2` when the field has `2^(2n)` elements), `herm` is an
involutive anti-automorphism of the matrix ring, which makes the set of matrices
`A` with `Aᴴ J A = J` and `det A = 1` a subgroup `SU3 n` of `GL(3, 2^(2n))`.
-/
import Mathlib
import ChallengeDeps
import Submission.Work.Models.Port.PSU3.Basic
import Submission.Work.Models.Port.Commons.FieldTheory.FiniteField.galoisField_pow_two_pow_succ_succ

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false

open Matrix LeanEval.GroupTheory.Defs

namespace Submission.PSU3

/-- The `(2^n)`-Frobenius automorphism of `GF(2^(2n))`. -/
noncomputable def frob (n : ℕ) : F n →+* F n where
  toFun x := x ^ (2 ^ n)
  map_one' := one_pow _
  map_mul' x y := mul_pow x y _
  map_zero' := zero_pow (pow_ne_zero _ (by norm_num))
  map_add' x y := add_pow_char_pow x y 2 n

lemma frob_apply (n : ℕ) (x : F n) : frob n x = x ^ (2 ^ n) := rfl

/-- `herm` is the transpose composed with the `(2^n)`-Frobenius. -/
lemma herm_eq_transpose_map (n : ℕ) (A : Matrix (Fin 3) (Fin 3) (F n)) :
    herm A = Aᵀ.map (frob n) := by
  ext i j
  simp [herm, frob_apply]

/-- `herm (herm A) = A`. -/
lemma herm_herm (n : ℕ) (A : Matrix (Fin 3) (Fin 3) (F n)) :
    herm (herm A) = A := by
  rcases eq_or_ne n 0 with rfl | hn
  · ext i j
    simp [herm]
  · ext i j
    show (A i j ^ 2 ^ n) ^ 2 ^ n = A i j
    rw [← pow_mul, show 2 ^ n * 2 ^ n = 2 ^ (2 * n) by rw [← pow_add]; ring]
    exact Commons.FieldTheory.FiniteField.galoisField_pow_card_pow_self (p := 2) (2 * n)
      (by omega) (A i j)

/-- `herm` reverses the order of a product. -/
lemma herm_mul (n : ℕ) (A B : Matrix (Fin 3) (Fin 3) (F n)) :
    herm (A * B) = herm B * herm A := by
  rw [herm_eq_transpose_map, herm_eq_transpose_map, herm_eq_transpose_map,
    Matrix.transpose_mul, Matrix.map_mul]

lemma herm_one (n : ℕ) : herm (1 : Matrix (Fin 3) (Fin 3) (F n)) = 1 := by
  rw [herm_eq_transpose_map, Matrix.transpose_one]
  exact Matrix.map_one (frob n) (frob n).map_zero (frob n).map_one

/-- The Gram matrix `J3` is fixed by `herm`. -/
lemma herm_J3 (n : ℕ) : herm (J3 : Matrix (Fin 3) (Fin 3) (F n)) = J3 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [herm, J3, frob_apply]

lemma J3_mul_self (n : ℕ) : (J3 : Matrix (Fin 3) (Fin 3) (F n)) * J3 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [J3, Matrix.mul_apply, Fin.sum_univ_three]

/-- `det (herm A) = (det A) ^ (2^n)`. -/
lemma det_herm (n : ℕ) (A : Matrix (Fin 3) (Fin 3) (F n)) :
    (herm A).det = A.det ^ (2 ^ n) := by
  rw [herm_eq_transpose_map]
  have := RingHom.map_det (frob n) Aᵀ
  rw [show ((frob n).mapMatrix Aᵀ) = Aᵀ.map (frob n) from rfl] at this
  rw [← this, Matrix.det_transpose]
  rfl

/-- `herm A⁻¹ = (herm A)⁻¹` for invertible `A`. -/
lemma herm_inv (n : ℕ) (A : Matrix (Fin 3) (Fin 3) (F n)) (hA : IsUnit A.det) :
    herm A⁻¹ = (herm A)⁻¹ := by
  symm
  refine Matrix.inv_eq_left_inv ?_
  rw [← herm_mul, Matrix.mul_nonsing_inv A hA, herm_one]

/-! ## `SU(3, 2^n)` as a subgroup -/

/-- The special unitary group `SU3 n ≤ GL(3, 2^(2n))`: the matrices `A` with `Aᴴ J A = J` and
`det A = 1`. -/
noncomputable def SU3 (n : ℕ) : Subgroup (GL (Fin 3) (F n)) where
  carrier := {A | IsSU3 A}
  mul_mem' := by
    intro A B hA hB
    obtain ⟨hA1, hA2⟩ := hA
    obtain ⟨hB1, hB2⟩ := hB
    have e : ((A * B : GL (Fin 3) (F n)) : Matrix (Fin 3) (Fin 3) (F n)) =
        (A : Matrix (Fin 3) (Fin 3) (F n)) * (B : Matrix (Fin 3) (Fin 3) (F n)) :=
      Matrix.GeneralLinearGroup.coe_mul A B
    refine ⟨?_, ?_⟩
    · rw [e, herm_mul]
      calc herm (B : Matrix (Fin 3) (Fin 3) (F n)) * herm (A : Matrix (Fin 3) (Fin 3) (F n)) *
            (J3 : Matrix (Fin 3) (Fin 3) (F n)) *
            ((A : Matrix (Fin 3) (Fin 3) (F n)) * (B : Matrix (Fin 3) (Fin 3) (F n)))
          = herm (B : Matrix (Fin 3) (Fin 3) (F n)) *
              (herm (A : Matrix (Fin 3) (Fin 3) (F n)) *
                (J3 : Matrix (Fin 3) (Fin 3) (F n)) *
                (A : Matrix (Fin 3) (Fin 3) (F n))) *
              (B : Matrix (Fin 3) (Fin 3) (F n)) := by noncomm_ring
        _ = herm (B : Matrix (Fin 3) (Fin 3) (F n)) * (J3 : Matrix (Fin 3) (Fin 3) (F n)) *
              (B : Matrix (Fin 3) (Fin 3) (F n)) := by rw [hA1]
        _ = J3 := hB1
    · rw [map_mul, hA2, hB2, mul_one]
  one_mem' := by
    refine ⟨?_, ?_⟩
    · rw [Matrix.GeneralLinearGroup.coe_one, herm_one, one_mul, mul_one]
    · exact map_one GeneralLinearGroup.det
  inv_mem' := by
    intro A hA
    obtain ⟨hA1, hA2⟩ := hA
    have hinvA : (A : Matrix (Fin 3) (Fin 3) (F n))⁻¹ =
        (J3 : Matrix (Fin 3) (Fin 3) (F n)) *
          herm (A : Matrix (Fin 3) (Fin 3) (F n)) *
          (J3 : Matrix (Fin 3) (Fin 3) (F n)) := by
      refine Matrix.inv_eq_left_inv ?_
      calc (J3 : Matrix (Fin 3) (Fin 3) (F n)) *
              herm (A : Matrix (Fin 3) (Fin 3) (F n)) *
              (J3 : Matrix (Fin 3) (Fin 3) (F n)) * (A : Matrix (Fin 3) (Fin 3) (F n))
          = (J3 : Matrix (Fin 3) (Fin 3) (F n)) *
              (herm (A : Matrix (Fin 3) (Fin 3) (F n)) *
                (J3 : Matrix (Fin 3) (Fin 3) (F n)) *
                (A : Matrix (Fin 3) (Fin 3) (F n))) := by noncomm_ring
        _ = (J3 : Matrix (Fin 3) (Fin 3) (F n)) * (J3 : Matrix (Fin 3) (Fin 3) (F n)) := by
              rw [hA1]
        _ = 1 := J3_mul_self n
    have hherm : herm ((A : Matrix (Fin 3) (Fin 3) (F n))⁻¹) =
        (J3 : Matrix (Fin 3) (Fin 3) (F n)) * (A : Matrix (Fin 3) (Fin 3) (F n)) *
          (J3 : Matrix (Fin 3) (Fin 3) (F n)) := by
      rw [hinvA]
      simp only [herm_mul, herm_herm, herm_J3]
      noncomm_ring
    refine ⟨?_, ?_⟩
    · rw [Matrix.GeneralLinearGroup.coe_inv, hherm, hinvA]
      calc ((J3 : Matrix (Fin 3) (Fin 3) (F n)) * (A : Matrix (Fin 3) (Fin 3) (F n)) *
              (J3 : Matrix (Fin 3) (Fin 3) (F n))) * (J3 : Matrix (Fin 3) (Fin 3) (F n)) *
              ((J3 : Matrix (Fin 3) (Fin 3) (F n)) *
                herm (A : Matrix (Fin 3) (Fin 3) (F n)) *
                (J3 : Matrix (Fin 3) (Fin 3) (F n)))
          = (J3 : Matrix (Fin 3) (Fin 3) (F n)) * (A : Matrix (Fin 3) (Fin 3) (F n)) *
              ((J3 : Matrix (Fin 3) (Fin 3) (F n)) * (J3 : Matrix (Fin 3) (Fin 3) (F n))) *
              ((J3 : Matrix (Fin 3) (Fin 3) (F n)) *
                herm (A : Matrix (Fin 3) (Fin 3) (F n)) *
                (J3 : Matrix (Fin 3) (Fin 3) (F n))) := by noncomm_ring
        _ = (J3 : Matrix (Fin 3) (Fin 3) (F n)) * (A : Matrix (Fin 3) (Fin 3) (F n)) * 1 *
              ((J3 : Matrix (Fin 3) (Fin 3) (F n)) *
                herm (A : Matrix (Fin 3) (Fin 3) (F n)) *
                (J3 : Matrix (Fin 3) (Fin 3) (F n))) := by rw [J3_mul_self n]
        _ = (J3 : Matrix (Fin 3) (Fin 3) (F n)) * (A : Matrix (Fin 3) (Fin 3) (F n)) *
              ((J3 : Matrix (Fin 3) (Fin 3) (F n)) *
                herm (A : Matrix (Fin 3) (Fin 3) (F n)) *
                (J3 : Matrix (Fin 3) (Fin 3) (F n))) := by rw [mul_one]
        _ = (J3 : Matrix (Fin 3) (Fin 3) (F n)) * (A : Matrix (Fin 3) (Fin 3) (F n)) *
              (A : Matrix (Fin 3) (Fin 3) (F n))⁻¹ := by rw [← hinvA]
        _ = (J3 : Matrix (Fin 3) (Fin 3) (F n)) *
              ((A : Matrix (Fin 3) (Fin 3) (F n)) * (A : Matrix (Fin 3) (Fin 3) (F n))⁻¹) := by
              noncomm_ring
        _ = (J3 : Matrix (Fin 3) (Fin 3) (F n)) * 1 := by
              rw [← Matrix.GeneralLinearGroup.coe_inv, ← Matrix.GeneralLinearGroup.coe_mul,
                mul_inv_cancel, Matrix.GeneralLinearGroup.coe_one]
        _ = J3 := by rw [mul_one]
    · rw [map_inv, hA2, inv_one]

/-- `PSU3Model n` is the image of `SU3 n` under the projection to `PGL`. -/
theorem PSU3Model_eq_map_SU3 (n : ℕ) :
    PSU3Model n = (SU3 n).map ProjGenLinGroup.mk := by
  rw [PSU3Model_eq]
  have h : Subgroup.closure {A : GL (Fin 3) (F n) | IsSU3 A} = SU3 n :=
    le_antisymm ((Subgroup.closure_le (SU3 n)).mpr (fun _ hx => hx)) Subgroup.subset_closure
  rw [h]

end Submission.PSU3
