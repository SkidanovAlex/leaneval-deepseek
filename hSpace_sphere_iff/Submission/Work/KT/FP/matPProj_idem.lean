import Mathlib
import Submission.Work.KT.FP.PencilDefs
import Submission.Work.KT.FP.pencil_local_annulus
import Submission.Work.KT.FP.pCirc_eq_of_annulus
import Submission.Work.KT.FP.pCirc_mul_pCirc

/-!
# `Work.KT.FP.matPProj_idem` — idempotency of the matrix pencil projection

The target lemma states that the pencil projection `matPProj X N A B ρ` of a matrix pencil
`z ↦ z • A + B` over `C(X, ℂ)`, whose invertibility locus contains the closed annulus
`ρ ≤ ‖z‖ ≤ 1`, is idempotent.

The mathematical content is one-dimensional and independent of the matrix structure, so we prove it
once for an abstract Banach algebra `R` (`pProj_mul_self_gen`) and then specialise it to the
`L∞` operator norm on `Matrix (Fin N) (Fin N) C(X, ℂ)`.

The abstract proof is the classical two-contour argument:

* `pencil_local_annulus` thickens the annulus of invertibility of `z • A + B` to an open-ended one
  `r ≤ ‖z‖ ≤ s` with `r < ρ < s`;
* `pCirc_eq_of_annulus` (deformation invariance) identifies `pCirc` at the radii `ρ`, `r` and `s`;
* `pCirc_mul_pCirc` gives the two-circle computation `pCirc r * pCirc s = (2πi) • pCirc r`, i.e.
  `P_r P_s = P_r` after normalising by `(2πi)⁻¹`;
* since `P_r = P_ρ = P_s` by deformation invariance, `P_ρ P_ρ = P_ρ`.
-/

namespace Work.KT.FP

open Matrix MeasureTheory intervalIntegral
open scoped Topology Interval

noncomputable section

/-- `(2πi)⁻¹ * (2πi)⁻¹ * (2πi) = (2πi)⁻¹`. -/
private lemma proj_scalar_mul :
    (2 * Real.pi * Complex.I : ℂ)⁻¹ * (2 * Real.pi * Complex.I : ℂ)⁻¹ *
      (2 * Real.pi * Complex.I : ℂ) = (2 * Real.pi * Complex.I : ℂ)⁻¹ := by
  have hne : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by
    refine mul_ne_zero (mul_ne_zero (by norm_num) ?_) Complex.I_ne_zero
    exact Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have h1 : (2 * Real.pi * Complex.I : ℂ)⁻¹ * (2 * Real.pi * Complex.I : ℂ) = 1 :=
    inv_mul_cancel₀ hne
  calc (2 * Real.pi * Complex.I : ℂ)⁻¹ * (2 * Real.pi * Complex.I : ℂ)⁻¹ *
        (2 * Real.pi * Complex.I : ℂ)
      = (2 * Real.pi * Complex.I : ℂ)⁻¹ * ((2 * Real.pi * Complex.I : ℂ)⁻¹ *
          (2 * Real.pi * Complex.I : ℂ)) := by ring
    _ = (2 * Real.pi * Complex.I : ℂ)⁻¹ * 1 := by rw [h1]
    _ = (2 * Real.pi * Complex.I : ℂ)⁻¹ := by ring

/-- **The Riesz (pencil) projection of a linear pencil is idempotent.**

If the pencil `z ↦ z • A + B` is invertible on the closed annulus `ρ ≤ ‖z‖ ≤ 1` (`0 < ρ ≤ 1`),
then `pProj A B ρ = (2πi)⁻¹ • ∮_{|z| = ρ} (zA + B)⁻¹ A dz` is a projection. -/
theorem pProj_mul_self_gen {R : Type*} [NormedRing R] [NormedAlgebra ℂ R] [CompleteSpace R]
    (A B : R) {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 1)
    (hunit : ∀ z : ℂ, ρ ≤ ‖z‖ → ‖z‖ ≤ 1 → IsUnit (z • A + B)) :
    pProj A B ρ * pProj A B ρ = pProj A B ρ := by
  obtain ⟨r, s, hr0, hrρ, hρs, hunit'⟩ := pencil_local_annulus A B hρ0 hρ1 hunit
  have hrρ' : r ≤ ρ := le_of_lt hrρ
  have hρs' : ρ ≤ s := le_of_lt hρs
  -- deformation invariance of the contour integral, to the radii `r` and `s`
  have hdefr : pCirc A B ρ = pCirc A B r :=
    pCirc_eq_of_annulus A B hr0 hrρ'
      (fun z hz1 hz2 => hunit' z hz1 (le_trans hz2 hρs'))
  have hdefs : pCirc A B s = pCirc A B ρ :=
    pCirc_eq_of_annulus A B hρ0 hρs'
      (fun z hz1 hz2 => hunit' z (le_trans hrρ' hz1) hz2)
  -- the two-circle computation at the radii `r < s`
  have htwo : pCirc A B r * pCirc A B s =
      (2 * Real.pi * Complex.I : ℂ) • pCirc A B r :=
    pCirc_mul_pCirc A B hr0 (hrρ.trans hρs) hunit'
  have hPr : pProj A B r = pProj A B ρ := by simp only [pProj]; rw [hdefr]
  have hPs : pProj A B s = pProj A B ρ := by simp only [pProj]; rw [hdefs]
  have htwo' : pProj A B r * pProj A B s = pProj A B r := by
    calc pProj A B r * pProj A B s
        = ((2 * Real.pi * Complex.I : ℂ)⁻¹ * (2 * Real.pi * Complex.I : ℂ)⁻¹) •
            (pCirc A B r * pCirc A B s) := by
          simp only [pProj]; rw [smul_mul_smul_comm]
      _ = ((2 * Real.pi * Complex.I : ℂ)⁻¹ * (2 * Real.pi * Complex.I : ℂ)⁻¹) •
            ((2 * Real.pi * Complex.I : ℂ) • pCirc A B r) := by rw [htwo]
      _ = (((2 * Real.pi * Complex.I : ℂ)⁻¹ * (2 * Real.pi * Complex.I : ℂ)⁻¹) *
            (2 * Real.pi * Complex.I : ℂ)) • pCirc A B r := by rw [smul_smul]
      _ = (2 * Real.pi * Complex.I : ℂ)⁻¹ • pCirc A B r := by rw [proj_scalar_mul]
      _ = pProj A B r := by simp only [pProj]
  calc pProj A B ρ * pProj A B ρ
      = pProj A B r * pProj A B s := by rw [hPr, hPs]
    _ = pProj A B r := htwo'
    _ = pProj A B ρ := hPr

/-- **`Work.KT.FP.matPProj_idem`.**  The pencil projection of a matrix pencil over `C(X, ℂ)`,
with the `L∞` operator norm, is idempotent, provided `z • A + B` is invertible on the closed
annulus `ρ ≤ ‖z‖ ≤ 1`. -/
theorem matPProj_idem (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X]
    {N : ℕ} (A B : Matrix (Fin N) (Fin N) C(X, ℂ)) {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 1)
    (hunit : ∀ z : ℂ, ρ ≤ ‖z‖ → ‖z‖ ≤ 1 → IsUnit (z • A + B)) :
    matPProj X N A B ρ * matPProj X N A B ρ = matPProj X N A B ρ := by
  letI : NormedRing (Matrix (Fin N) (Fin N) C(X, ℂ)) := Matrix.linftyOpNormedRing
  letI : NormedAlgebra ℂ (Matrix (Fin N) (Fin N) C(X, ℂ)) := Matrix.linftyOpNormedAlgebra
  letI : CompleteSpace (Matrix (Fin N) (Fin N) C(X, ℂ)) := Matrix.instCompleteSpace _ _ _
  have hC : CompleteSpace (Matrix (Fin N) (Fin N) C(X, ℂ)) := inferInstance
  exact @pProj_mul_self_gen (Matrix (Fin N) (Fin N) C(X, ℂ))
    Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra hC A B ρ hρ0 hρ1 hunit

end

end Work.KT.FP
