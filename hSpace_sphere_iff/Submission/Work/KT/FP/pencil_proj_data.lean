import Mathlib
import Submission.Work.KT.FP.PencilDefs
import Submission.Work.KT.FP.pencil_local_annulus
import Submission.Work.KT.FP.pCirc_eq_of_annulus
import Submission.Work.KT.FP.pCirc_mul_pCirc

namespace Work.KT.FP

open MeasureTheory intervalIntegral
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

variable {R : Type*} [NormedRing R] [NormedAlgebra ℂ R] [CompleteSpace R]

theorem pencil_proj_data {R : Type*} [NormedRing R] [NormedAlgebra ℂ R] [CompleteSpace R]
    (A₀ B₀ : R) :
    (∀ {ρ : ℝ}, 0 < ρ → ρ ≤ 1 →
      (∀ z : ℂ, ρ ≤ ‖z‖ → ‖z‖ ≤ 1 → IsUnit (z • A₀ + B₀)) →
      pProj A₀ B₀ ρ * pProj A₀ B₀ ρ = pProj A₀ B₀ ρ) ∧
    (∀ {ρ₁ ρ₂ : ℝ}, 0 < ρ₁ → ρ₁ < ρ₂ → ρ₂ ≤ 1 →
      (∀ z : ℂ, ρ₁ ≤ ‖z‖ → ‖z‖ ≤ ρ₂ → IsUnit (z • A₀ + B₀)) →
      pProj A₀ B₀ ρ₁ = pProj A₀ B₀ ρ₂) := by
  constructor
  · intro ρ hρ0 hρ1 hunit
    obtain ⟨r, s, hr0, hrρ, hρs, hunit'⟩ := pencil_local_annulus A₀ B₀ hρ0 hρ1 hunit
    have hrρ' : r ≤ ρ := le_of_lt hrρ
    have hρs' : ρ ≤ s := le_of_lt hρs
    -- deformation invariance of the contour integral, to radii `r` and `s`
    have hdefr : pCirc A₀ B₀ ρ = pCirc A₀ B₀ r :=
      pCirc_eq_of_annulus A₀ B₀ hr0 hrρ'
        (fun z hz1 hz2 => hunit' z hz1 (le_trans hz2 hρs'))
    have hdefs : pCirc A₀ B₀ s = pCirc A₀ B₀ ρ :=
      pCirc_eq_of_annulus A₀ B₀ hρ0 hρs'
        (fun z hz1 hz2 => hunit' z (le_trans hrρ' hz1) hz2)
    -- the two-circle computation at radii `r < s`
    have htwo : pCirc A₀ B₀ r * pCirc A₀ B₀ s =
        (2 * Real.pi * Complex.I : ℂ) • pCirc A₀ B₀ r :=
      pCirc_mul_pCirc A₀ B₀ hr0 (hrρ.trans hρs) hunit'
    have hPr : pProj A₀ B₀ r = pProj A₀ B₀ ρ := by
      simp only [pProj]
      rw [hdefr]
    have hPs : pProj A₀ B₀ s = pProj A₀ B₀ ρ := by
      simp only [pProj]
      rw [hdefs]
    have htwo' : pProj A₀ B₀ r * pProj A₀ B₀ s = pProj A₀ B₀ r := by
      calc pProj A₀ B₀ r * pProj A₀ B₀ s
          = ((2 * Real.pi * Complex.I : ℂ)⁻¹ * (2 * Real.pi * Complex.I : ℂ)⁻¹) •
              (pCirc A₀ B₀ r * pCirc A₀ B₀ s) := by
            simp only [pProj]
            rw [smul_mul_smul_comm]
        _ = ((2 * Real.pi * Complex.I : ℂ)⁻¹ * (2 * Real.pi * Complex.I : ℂ)⁻¹) •
              ((2 * Real.pi * Complex.I : ℂ) • pCirc A₀ B₀ r) := by rw [htwo]
        _ = (((2 * Real.pi * Complex.I : ℂ)⁻¹ * (2 * Real.pi * Complex.I : ℂ)⁻¹) *
              (2 * Real.pi * Complex.I : ℂ)) • pCirc A₀ B₀ r := by rw [smul_smul]
        _ = (2 * Real.pi * Complex.I : ℂ)⁻¹ • pCirc A₀ B₀ r := by rw [proj_scalar_mul]
        _ = pProj A₀ B₀ r := by simp only [pProj]
    calc pProj A₀ B₀ ρ * pProj A₀ B₀ ρ
        = pProj A₀ B₀ r * pProj A₀ B₀ s := by rw [hPr, hPs]
      _ = pProj A₀ B₀ r := htwo'
      _ = pProj A₀ B₀ ρ := hPr
  · intro ρ₁ ρ₂ hρ₁ hlt hρ₂ hunit
    have h : pCirc A₀ B₀ ρ₂ = pCirc A₀ B₀ ρ₁ :=
      pCirc_eq_of_annulus A₀ B₀ hρ₁ (le_of_lt hlt) hunit
    simp only [pProj]
    rw [h]

end

end Work.KT.FP
