import Mathlib
import Submission.Work.Modular.GroupAlgebra
import Submission.Work.Modular.sigmaAlg_basisElem_row

namespace Work.Modular

open Work.Modular
open scoped MonoidAlgebra

/-- The linear map `r ↦ (σ r) 0` (row `0` of the six-dimensional representation `σ`). -/
noncomputable def Lrow : GroupRing →ₗ[ℂ] (Fin 6 → ℂ) :=
  (LinearMap.proj (0 : Fin 6)).comp
    (sigmaAlg : GroupRing →ₗ[ℂ] Matrix (Fin 6) (Fin 6) ℂ)

lemma Lrow_apply (r : GroupRing) : Lrow r = (sigmaAlg r) 0 := rfl

/-- The linear functional `r ↦ (σ r) 0 1`, the matrix coefficient in row `0`, column `1`. -/
noncomputable def phiRow : GroupRing →ₗ[ℂ] ℂ :=
  (LinearMap.proj (1 : Fin 6)).comp Lrow

lemma phiRow_apply (r : GroupRing) : phiRow r = (sigmaAlg r) 0 1 := rfl

/-- Row `0` of `(σ T - 1)^2` vanishes. -/
lemma sigmaT_sub_one_sq_row0 : (((sigmaT - 1) ^ 2 : Matrix (Fin 6) (Fin 6) ℂ)) 0 = 0 := by
  ext j
  fin_cases j <;>
    simp [pow_two, Matrix.mul_apply, Matrix.sub_apply, Matrix.one_apply, Fin.sum_univ_six,
      sigmaT] <;> norm_num

/-- Row `3` of `(σ T - 1)^2` vanishes. -/
lemma sigmaT_sub_one_sq_row3 : (((sigmaT - 1) ^ 2 : Matrix (Fin 6) (Fin 6) ℂ)) 3 = 0 := by
  ext j
  fin_cases j <;>
    simp [pow_two, Matrix.mul_apply, Matrix.sub_apply, Matrix.one_apply, Fin.sum_univ_six,
      sigmaT] <;> norm_num

lemma sigmaAlg_sub_one_sq : sigmaAlg ((tR - 1) ^ 2) = (sigmaT - 1) ^ 2 := by
  simp only [map_pow, map_sub, map_one, sigmaAlg_tR]

/-- Row `0` of `σ S * (σ T - 1)^2` vanishes (it is row `3` of `(σ T - 1)^2`). -/
lemma sigmaS_mul_sub_one_sq_row0 :
    ((sigmaS * (sigmaT - 1) ^ 2) : Matrix (Fin 6) (Fin 6) ℂ) 0 = 0 := by
  ext j
  simp [Matrix.mul_apply, Fin.sum_univ_six, sigmaS, sigmaT_sub_one_sq_row3]

/-- A matrix product whose left factor has vanishing row `0` has vanishing row `0`. -/
lemma mat_row0_mul_eq_zero {A B : Matrix (Fin 6) (Fin 6) ℂ} (hA : A 0 = 0) : (A * B) 0 = 0 := by
  ext j
  simp [Matrix.mul_apply, hA]

/-- The first `σ`-row vanishes on the right ideal `I`. -/
lemma sigmaAlg_idealI_row' {r : GroupRing} (hr : r ∈ idealI) : (sigmaAlg r) 0 = 0 := by
  have hle : idealI ≤ LinearMap.ker Lrow := by
    rw [idealI, Submodule.span_le]
    rintro x (⟨q, rfl⟩ | ⟨q, rfl⟩)
    · change (sigmaAlg ((tR - 1) ^ 2 * q)) 0 = 0
      rw [map_mul, sigmaAlg_sub_one_sq]
      exact mat_row0_mul_eq_zero sigmaT_sub_one_sq_row0
    · change (sigmaAlg (sR * (tR - 1) ^ 2 * q)) 0 = 0
      rw [map_mul, map_mul, sigmaAlg_sR, sigmaAlg_sub_one_sq]
      exact mat_row0_mul_eq_zero sigmaS_mul_sub_one_sq_row0
  exact hle hr

lemma phiRow_basisElem_self : phiRow (basisElem 1) = 1 := by
  rw [phiRow_apply, sigmaAlg_basisElem_row 1, Pi.single_eq_same]

lemma phiRow_basisElem_ne {i : Fin 6} (hi : i ≠ 1) : phiRow (basisElem i) = 0 := by
  rw [phiRow_apply, sigmaAlg_basisElem_row i, Pi.single_eq_of_ne' hi]

/-- The linear functional `φ r = (σ r) 0 1` vanishes on `I` and is the `T`-coordinate
functional on the quotient. -/
theorem exists_functional_T : ∃ φ : GroupRing →ₗ[ℂ] ℂ, (∀ r ∈ idealI, φ r = 0) ∧ φ 1 = 0 ∧
    φ tR = 1 ∧ φ (tR * sR) = 0 ∧ φ sR = 0 ∧ φ (sR * tR) = 0 ∧ φ (sR * tR * sR) = 0 := by
  refine ⟨phiRow, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro r hr
    rw [phiRow_apply]
    simpa using congrFun (sigmaAlg_idealI_row' hr) 1
  · rw [show (1 : GroupRing) = basisElem 0 by simp [basisElem]]
    exact phiRow_basisElem_ne (by decide : (0 : Fin 6) ≠ 1)
  · rw [show tR = basisElem 1 by simp [basisElem]]
    exact phiRow_basisElem_self
  · rw [show tR * sR = basisElem 2 by simp [basisElem]]
    exact phiRow_basisElem_ne (by decide : (2 : Fin 6) ≠ 1)
  · rw [show sR = basisElem 3 by simp [basisElem]]
    exact phiRow_basisElem_ne (by decide : (3 : Fin 6) ≠ 1)
  · rw [show sR * tR = basisElem 4 by simp [basisElem]]
    exact phiRow_basisElem_ne (by decide : (4 : Fin 6) ≠ 1)
  · rw [show sR * tR * sR = basisElem 5 by simp [basisElem]]
    exact phiRow_basisElem_ne (by decide : (5 : Fin 6) ≠ 1)

end Work.Modular
