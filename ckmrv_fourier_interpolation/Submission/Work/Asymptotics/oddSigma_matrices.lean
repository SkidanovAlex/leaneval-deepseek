import Mathlib
import Submission.Work.Asymptotics.OddSigmaMatrices

open Matrix

noncomputable section

namespace Work.Asymptotics

/-- The explicit product `S * T` in the same basis. -/
def oddMST : Matrix (Fin 6) (Fin 6) ℂ :=
  !![0, 0, 0, 2, -1, 0;
     -2, 0, -1, 4, -2, 0;
     0, 0, 0, -3, 2, 0;
     -2, 1, 0, 0, 0, 0;
     -4, 2, 0, -2, 0, 1;
     -3, 2, 0, 0, 0, 0]

/-- The explicit square `(S * T) ^ 2` in the same basis. -/
def oddMST2 : Matrix (Fin 6) (Fin 6) ℂ :=
  !![0, 0, 0, 2, 0, -1;
     0, 0, 0, 3, 0, -2;
     -2, 1, 0, -4, 0, 2;
     -2, 0, -1, 0, 0, 0;
     -3, 0, -2, 0, 0, 0;
     -4, 0, -2, 2, -1, 0]

/-- The explicit inverse of `oddMT`. -/
def oddMTi : Matrix (Fin 6) (Fin 6) ℂ :=
  !![0, 1, 0, 0, 0, 0;
     -1, 2, 0, 0, 0, 0;
     0, -2, 0, 0, 0, 1;
     0, 0, 0, 0, 1, 0;
     0, 0, 0, -1, 2, 0;
     0, 0, -1, 0, 2, 0]

lemma oddMS_mul_oddMT_eq : oddMS * oddMT = oddMST := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, oddMS, oddMT, oddMST, Fin.sum_univ_six] <;> norm_num

lemma oddMST_mul_oddMST_eq : oddMST * oddMST = oddMST2 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, oddMST, oddMST2, Fin.sum_univ_six] <;> norm_num

lemma oddMST2_mul_oddMST_eq : oddMST2 * oddMST = -1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, oddMST, oddMST2, Fin.sum_univ_six] <;> norm_num

lemma oddMT_mul_oddMTi : oddMT * oddMTi = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, oddMT, oddMTi, Fin.sum_univ_six]

lemma oddMTi_mul_oddMT : oddMTi * oddMT = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, oddMT, oddMTi, Fin.sum_univ_six]

lemma oddMT_inv : oddMT⁻¹ = oddMTi := Matrix.inv_eq_left_inv oddMTi_mul_oddMT

lemma oddMu_zero : oddMu 0 = 1 := rfl

lemma oddMu_one : oddMu 1 = oddMT⁻¹ := rfl

lemma oddMu_two : oddMu 2 = oddMS * oddMT * oddMS := rfl

lemma oddMu_three : oddMu 3 = oddMS := rfl

lemma oddMu_four : oddMu 4 = oddMS * oddMT⁻¹ := rfl

lemma oddMu_five : oddMu 5 = oddMT * oddMS := rfl

lemma oddMu_row0_zero (j : Fin 6) : (oddMu 0 : Matrix (Fin 6) (Fin 6) ℂ) 0 j =
    if j = 0 then 1 else 0 := by
  rw [oddMu_zero]
  fin_cases j <;> simp [Matrix.one_apply]

lemma oddMu_row0_one (j : Fin 6) : (oddMu 1 : Matrix (Fin 6) (Fin 6) ℂ) 0 j =
    if j = 1 then 1 else 0 := by
  rw [oddMu_one, oddMT_inv]
  fin_cases j <;> simp [oddMTi]

lemma oddMu_row0_two (j : Fin 6) : (oddMu 2 : Matrix (Fin 6) (Fin 6) ℂ) 0 j =
    if j = 2 then 1 else 0 := by
  rw [oddMu_two, oddMS_mul_oddMT_eq]
  fin_cases j <;>
    simp [Matrix.mul_apply, oddMST, oddMS, Fin.sum_univ_six]

lemma oddMu_row0_three (j : Fin 6) : (oddMu 3 : Matrix (Fin 6) (Fin 6) ℂ) 0 j =
    if j = 3 then 1 else 0 := by
  rw [oddMu_three]
  fin_cases j <;> simp [oddMS]

lemma oddMu_row0_four (j : Fin 6) : (oddMu 4 : Matrix (Fin 6) (Fin 6) ℂ) 0 j =
    if j = 4 then 1 else 0 := by
  rw [oddMu_four, oddMT_inv]
  fin_cases j <;>
    simp [Matrix.mul_apply, oddMS, oddMTi, Fin.sum_univ_six]

lemma oddMu_row0_five (j : Fin 6) : (oddMu 5 : Matrix (Fin 6) (Fin 6) ℂ) 0 j =
    if j = 5 then 1 else 0 := by
  rw [oddMu_five]
  fin_cases j <;>
    simp [Matrix.mul_apply, oddMT, oddMS, Fin.sum_univ_six]

/-- The five finite matrix identities satisfied by the explicit matrices `oddMS`, `oddMT`,
`oddMu` of `Submission.Work.Asymptotics.OddSigmaMatrices` (`R/𝓘_odd` in the basis
`(1, T⁻¹, STS, S, ST⁻¹, TS)`):

* `oddMS * oddMS = -1` and `(oddMS * oddMT) ^ 3 = -1`, i.e. `oddMS`, `oddMT` satisfy the
  relations of the classical presentation `SL(2,ℤ) = ⟨S,T | S⁴ = 1, S² = (ST)³⟩`, so that by
  the universal property of that presentation they define a representation
  `SL(2,ℤ) →* Matrix (Fin 6) (Fin 6) ℂ` with `S ↦ oddMS`, `T ↦ oddMT`, and `z = -I ↦ -1`;
* the `0`-th row of `(oddMT - 1) ^ 2` vanishes, and likewise the `0`-th row of
  `oddMS * (oddMT - 1) ^ 2`; these say that the "first-row functionals" of that
  representation annihilate the two ideal generators `(T-I)²` and `S(T-I)²`;
* the six matrices `oddMu i` have `(oddMu i) 0 j = δᵢⱼ`, i.e. the first-row functionals take
  the values `δᵢⱼ` on the six basis elements, which is the invertibility statement used in the
  CKMRV proof of Proposition 3.2(1).

All five are finite computations with explicit `6 × 6` matrices with rational entries; the
expected proof is `ext`/`fin_cases`/`norm_num` (or `decide` on the entrywise equalities).
For the last conjunct one should display `oddMT⁻¹` explicitly, e.g. by proving
`oddMT⁻¹ * oddMT = 1` entrywise and using `Matrix.inv_eq_left_inv`. -/
theorem oddSigma_matrices :
    (Work.Asymptotics.oddMS * Work.Asymptotics.oddMS = -1) ∧
      ((Work.Asymptotics.oddMS * Work.Asymptotics.oddMT) ^ 3 = -1) ∧
      (∀ j : Fin 6, ((Work.Asymptotics.oddMT - 1) ^ 2 : Matrix (Fin 6) (Fin 6) ℂ) 0 j = 0) ∧
      (∀ j : Fin 6,
        (Work.Asymptotics.oddMS * (Work.Asymptotics.oddMT - 1) ^ 2
          : Matrix (Fin 6) (Fin 6) ℂ) 0 j = 0) ∧
      (∀ i j : Fin 6, Work.Asymptotics.oddMu i 0 j = if j = i then 1 else 0) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, oddMS, Fin.sum_univ_six]
  · have h3 : (oddMS * oddMT) ^ 3
        = (oddMS * oddMT) * (oddMS * oddMT) * (oddMS * oddMT) := by
      simp only [pow_succ, pow_zero, one_mul]
    rw [h3, oddMS_mul_oddMT_eq, oddMST_mul_oddMST_eq, oddMST2_mul_oddMST_eq]
  · intro j
    fin_cases j <;>
      simp [Matrix.mul_apply, pow_succ, oddMT, Fin.sum_univ_six] <;> norm_num
  · intro j
    fin_cases j <;>
      simp [Matrix.mul_apply, pow_succ, oddMS, oddMT, Fin.sum_univ_six] <;> norm_num
  · intro i j
    fin_cases i
    · exact oddMu_row0_zero j
    · exact oddMu_row0_one j
    · exact oddMu_row0_two j
    · exact oddMu_row0_three j
    · exact oddMu_row0_four j
    · exact oddMu_row0_five j

end Work.Asymptotics

end
