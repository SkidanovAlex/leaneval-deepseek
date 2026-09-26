import Mathlib
import Submission.Work.SG.SGsepDefs

namespace Work.SGsep

open Work.SG
open Classical

set_option linter.style.haveILetI false

/-! ## Inversion lemmas for unimodular integer matrices

`invMat U = U.det • U.adjugate` is the two-sided inverse of `U` in the integer matrix ring
whenever `U.det` is a unit.  We record the facts needed to reverse an integral equivalence. -/

/-- For unimodular `U` the ring inverse agrees with `invMat`. -/
lemma inv_eq_invMat {U : IMat} (hU : IsUnit U.det) : U⁻¹ = invMat U := by
  have h1 : U⁻¹ * U = 1 := Matrix.nonsing_inv_mul U hU
  calc U⁻¹ = U⁻¹ * 1 := (mul_one _).symm
    _ = U⁻¹ * (U * invMat U) := by rw [mul_invMat hU]
    _ = (U⁻¹ * U) * invMat U := (mul_assoc _ _ _).symm
    _ = 1 * invMat U := by rw [h1]
    _ = invMat U := one_mul _

/-- `invMat` is an involution on unimodular matrices. -/
lemma nonsing_inv_invMat {U : IMat} (hU : IsUnit U.det) : (invMat U)⁻¹ = U := by
  have h1 : (invMat U)⁻¹ * invMat U = 1 :=
    Matrix.nonsing_inv_mul (invMat U) (isUnit_det_invMat hU)
  calc (invMat U)⁻¹ = (invMat U)⁻¹ * 1 := (mul_one _).symm
    _ = (invMat U)⁻¹ * (invMat U * U) := by rw [invMat_mul hU]
    _ = ((invMat U)⁻¹ * invMat U) * U := (mul_assoc _ _ _).symm
    _ = 1 * U := by rw [h1]
    _ = U := one_mul U

/-- `invMat U · (U C U⁻¹) = C · invMat U` for unimodular `U`. -/
lemma invMat_conj_eq {U C : IMat} (hU : IsUnit U.det) :
    invMat U * (U * C * U⁻¹) = C * invMat U := by
  rw [inv_eq_invMat hU]
  simp only [← Matrix.mul_assoc, invMat_mul hU, one_mul]

/-- Conjugating by `invMat U` inverts the original conjugation: `U⁻¹ (U C U⁻¹) U = C`. -/
lemma invMat_conj_apply {U C : IMat} (hU : IsUnit U.det) :
    invMat U * (U * C * U⁻¹) * (invMat U)⁻¹ = C := by
  rw [invMat_conj_eq hU, Matrix.mul_assoc,
    Matrix.mul_nonsing_inv (invMat U) (isUnit_det_invMat hU), Matrix.mul_one]

/-- Real version of `invMat_conj_eq`. -/
lemma toRMat_invMat_conj {U C : IMat} (hU : IsUnit U.det) :
    toRMat (invMat U) * toRMat (U * C * U⁻¹) = toRMat C * toRMat (invMat U) := by
  rw [← toRMat_mul, invMat_conj_eq hU, toRMat_mul]

/-- The real cast of a unimodular integer matrix acts on integer vectors. -/
lemma toRMat_mulVec_intVec (A : IMat) (v : IVec) :
    (toRMat A).mulVec (intVec v) = intVec (A.mulVec v) := mulVec_toRVec A v

/-- Reversing an integral equivalence: `IntEquiv P τ P' τ' U s` gives
`IntEquiv P' τ' P τ (invMat U) (-(toRMat (invMat U)).mulVec s)` (the reverse translation
`-U⁻¹ s`, with `U⁻¹ = invMat U`).  Useful matrix facts for `IsUnit U.det`:
`U * invMat U = 1`, `invMat U * U = 1` (`SGsepDefs`), `U⁻¹ = invMat U` (`Matrix.inv_def` plus
`Ring.inverse` of `±1`) and `invMat (invMat U) = U` (adjugate identities). -/
theorem IntEquiv_symm {P P' : Set IMat} {τ τ' : IMat → Fin 3 → ℝ} {U : IMat} {s : Fin 3 → ℝ}
    (hU : IsUnit U.det) (h : IntEquiv P τ P' τ' U s) :
    IntEquiv P' τ' P τ (invMat U) (-(toRMat (invMat U)).mulVec s) := by
  obtain ⟨hP, hτ⟩ := h
  refine ⟨?_, ?_⟩
  · intro A
    rw [nonsing_inv_invMat hU]
    constructor
    · intro hA
      refine ⟨U * A * U⁻¹, (hP _).mpr ⟨A, hA, rfl⟩, ?_⟩
      rw [invMat_conj_eq hU, Matrix.mul_assoc, invMat_mul hU, Matrix.mul_one]
    · rintro ⟨B, hB, rfl⟩
      obtain ⟨C, hC, rfl⟩ := (hP B).mp hB
      rw [invMat_conj_eq hU, Matrix.mul_assoc, invMat_mul hU, Matrix.mul_one]
      exact hC
  · intro B hB
    obtain ⟨C, hC, rfl⟩ := (hP B).mp hB
    obtain ⟨n, hn⟩ := hτ C hC
    refine ⟨-((invMat U).mulVec n), ?_⟩
    rw [invMat_conj_apply hU]
    have hVU : toRMat (invMat U) * toRMat U = 1 := by
      rw [← toRMat_mul, invMat_mul hU, toRMat_one]
    have hneg : intVec (-((invMat U).mulVec n)) = -intVec ((invMat U).mulVec n) := by
      funext i; simp [intVec]
    have h_expand : (toRMat (invMat U)).mulVec (τ' (U * C * U⁻¹))
        = τ C + (toRMat (invMat U)).mulVec s
          - (toRMat C).mulVec ((toRMat (invMat U)).mulVec s)
          + intVec ((invMat U).mulVec n) := by
      rw [hn]
      simp only [Matrix.mulVec_add, Matrix.mulVec_sub]
      rw [show (U.map (Int.cast : ℤ → ℝ)) = toRMat U from rfl,
          show ((U * C * U⁻¹).map (Int.cast : ℤ → ℝ)) = toRMat (U * C * U⁻¹) from rfl]
      rw [Matrix.mulVec_mulVec, hVU, Matrix.one_mulVec,
         Matrix.mulVec_mulVec, toRMat_invMat_conj hU, ← Matrix.mulVec_mulVec,
         toRMat_mulVec_intVec]
    rw [show (Matrix.map (invMat U) (Int.cast : ℤ → ℝ) : Matrix (Fin 3) (Fin 3) ℝ)
          = toRMat (invMat U) from rfl,
        show (Matrix.map C (Int.cast : ℤ → ℝ) : Matrix (Fin 3) (Fin 3) ℝ)
          = toRMat C from rfl]
    rw [h_expand, Matrix.mulVec_neg, hneg]
    abel

end Work.SGsep
