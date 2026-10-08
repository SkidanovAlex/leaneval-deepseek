import Mathlib
import Submission.Work.DSTR.M110.torusFrobDefs

open Matrix

namespace Work.DSTR.M110

variable {F : Type*} [Field F]

/-- For a matrix `B` with `B * B = c • 1`, the "column matrix" `!![0, B 0 1; 1, B 1 1]`
satisfies the relation `B * T = T * companionMat c`. This is the matrix form of the statement
that `T` is the matrix of the basis `(e₁, B e₁)`. -/
lemma mul_colMat_caseA (B : Matrix (Fin 2) (Fin 2) F) (c : F) (hB : B * B = c • 1) :
    B * (!![0, B 0 1; 1, B 1 1] : Matrix (Fin 2) (Fin 2) F)
      = (!![0, B 0 1; 1, B 1 1] : Matrix (Fin 2) (Fin 2) F) * companionMat c := by
  have h01 : B 0 0 * B 0 1 + B 0 1 * B 1 1 = 0 := by
    have := congrFun (congrFun hB 0) 1
    simpa [Matrix.mul_apply, Fin.sum_univ_two] using this
  have h11 : B 1 0 * B 0 1 + B 1 1 * B 1 1 = c := by
    have := congrFun (congrFun hB 1) 1
    simpa [Matrix.mul_apply, Fin.sum_univ_two] using this
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, h01, h11]

/-- For a matrix `B` with `B * B = c • 1`, the "column matrix" `!![1, B 0 0; 0, B 1 0]`
satisfies the relation `B * T = T * companionMat c`. This is the matrix form of the statement
that `T` is the matrix of the basis `(e₀, B e₀)`. -/
lemma mul_colMat_caseB (B : Matrix (Fin 2) (Fin 2) F) (c : F) (hB : B * B = c • 1) :
    B * (!![1, B 0 0; 0, B 1 0] : Matrix (Fin 2) (Fin 2) F)
      = (!![1, B 0 0; 0, B 1 0] : Matrix (Fin 2) (Fin 2) F) * companionMat c := by
  have h00 : B 0 0 * B 0 0 + B 0 1 * B 1 0 = c := by
    have := congrFun (congrFun hB 0) 0
    simpa [Matrix.mul_apply, Fin.sum_univ_two] using this
  have h10 : B 1 0 * B 0 0 + B 1 1 * B 1 0 = 0 := by
    have := congrFun (congrFun hB 1) 0
    simpa [Matrix.mul_apply, Fin.sum_univ_two] using this
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, h00, h10]

/-- If `B * T = T * companionMat c` for an invertible `T` (and `c ≠ 0`), then `B` is conjugate
to `companionMat c`. -/
lemma exists_conj_of_mul_eq (B T : Matrix (Fin 2) (Fin 2) F) (c : F)
    (hdet : T.det ≠ 0) (hc0 : c ≠ 0)
    (h : B * T = T * companionMat c) :
    ∃ S : GL (Fin 2) F,
      (S : Matrix (Fin 2) (Fin 2) F) * B * (S : Matrix (Fin 2) (Fin 2) F)⁻¹ = companionMat c := by
  have hMdet : (companionMat c).det ≠ 0 := companionMat_det hc0
  let u : GL (Fin 2) F := Matrix.GeneralLinearGroup.mkOfDetNeZero T hdet
  have hu : (u : Matrix (Fin 2) (Fin 2) F) = T :=
    Matrix.GeneralLinearGroup.val_mkOfDetNeZero T hdet
  refine ⟨u⁻¹, ?_⟩
  have hmm : (u : Matrix (Fin 2) (Fin 2) F)⁻¹ * (u : Matrix (Fin 2) (Fin 2) F) = 1 := by
    rw [← Matrix.GeneralLinearGroup.coe_inv u, ← Matrix.GeneralLinearGroup.coe_mul,
      inv_mul_cancel u, Matrix.GeneralLinearGroup.coe_one]
  rw [← Matrix.GeneralLinearGroup.coe_inv (u⁻¹)]
  simp only [inv_inv]
  rw [Matrix.GeneralLinearGroup.coe_inv u]
  calc (u : Matrix (Fin 2) (Fin 2) F)⁻¹ * B * (u : Matrix (Fin 2) (Fin 2) F)
      = (u : Matrix (Fin 2) (Fin 2) F)⁻¹ * (B * (u : Matrix (Fin 2) (Fin 2) F)) := by
        rw [mul_assoc]
    _ = (u : Matrix (Fin 2) (Fin 2) F)⁻¹ * ((u : Matrix (Fin 2) (Fin 2) F) * companionMat c) := by
        rw [hu, h]
    _ = ((u : Matrix (Fin 2) (Fin 2) F)⁻¹ * (u : Matrix (Fin 2) (Fin 2) F)) * companionMat c := by
        rw [mul_assoc]
    _ = companionMat c := by rw [hmm, one_mul]

/-- **Companion reduction (general field).**  A matrix `B ∈ M₂(F)` with `B * B = c • 1` and `c`
a non-square is conjugate to the companion matrix of `X ^ 2 - c`.  The hypothesis that `c` is a
non-square is used to find a vector `v` with `(v, B v)` a basis (`B` cannot be scalar). -/
lemma exists_conj_companion (c : F) (hc : ¬ IsSquare c) (B : Matrix (Fin 2) (Fin 2) F)
    (hB : B * B = c • 1) :
    ∃ S : GL (Fin 2) F,
      (S : Matrix (Fin 2) (Fin 2) F) * B * (S : Matrix (Fin 2) (Fin 2) F)⁻¹ = companionMat c := by
  have hc0 : c ≠ 0 := ne_zero_of_not_isSquare hc
  rcases eq_or_ne (B 0 1) 0 with hb | hb
  · -- `B 0 1 = 0`: then `B 1 0 ≠ 0` and we conjugate with the basis `(e₀, B e₀)`.
    have h00 : B 0 0 * B 0 0 + B 0 1 * B 1 0 = c := by
      have := congrFun (congrFun hB 0) 0
      simpa [Matrix.mul_apply, Fin.sum_univ_two] using this
    have hd : B 1 0 ≠ 0 := by
      intro hd0
      exact hc ⟨B 0 0, by rw [← h00, hb, hd0]; simp⟩
    exact exists_conj_of_mul_eq B (!![1, B 0 0; 0, B 1 0] : Matrix (Fin 2) (Fin 2) F) c
      (by simpa [Matrix.det_fin_two] using hd) hc0 (mul_colMat_caseB B c hB)
  · -- `B 0 1 ≠ 0`: we conjugate with the basis `(e₁, B e₁)`.
    exact exists_conj_of_mul_eq B (!![0, B 0 1; 1, B 1 1] : Matrix (Fin 2) (Fin 2) F) c
      (by simpa [Matrix.det_fin_two, neg_eq_zero] using hb) hc0 (mul_colMat_caseA B c hB)

end Work.DSTR.M110

namespace Work.DSTR.M110

theorem companionConjProof (p k : ℕ) [Fact p.Prime] (hk : k ≠ 0) [DecidableEq (GaloisField p k)]
    (B : GL (Fin 2) (GaloisField p k)) (c : GaloisField p k)
    (hB : (B : Matrix (Fin 2) (Fin 2) (GaloisField p k)) * B = c • 1)
    (hc : ¬ IsSquare c) :
    ∃ S : GL (Fin 2) (GaloisField p k),
      (S : Matrix (Fin 2) (Fin 2) (GaloisField p k)) *
          (B : Matrix (Fin 2) (Fin 2) (GaloisField p k)) *
          (S : Matrix (Fin 2) (Fin 2) (GaloisField p k))⁻¹
        = Work.DSTR.M110.companionMat c := by
  exact exists_conj_companion (F := GaloisField p k) c hc
    (B : Matrix (Fin 2) (Fin 2) (GaloisField p k)) hB

end Work.DSTR.M110
