import Mathlib
import Submission.Work.TMComp.Duality.Defs
import Submission.Work.TMComp.Duality.twistU_mul
import Submission.Work.TMComp.Duality.twistU_intertwines

/-!
# Aubry duality (C3): the spectral form of the twist

The twist `U` intertwines the suspension at coupling `λ` with the suspension at coupling
`λ⁻¹`, scaled by `λ`.
-/

open LeanEval.Analysis.TenMartini

open scoped Pointwise

noncomputable section

namespace Work.TMComp.Duality

/-- Membership form of the scaling of the spectrum by a nonzero scalar. -/
theorem smul_mem_spectrum_iff (c : ℂ) (hc : c ≠ 0) (M : EllTwo2 →L[ℂ] EllTwo2) (z : ℂ) :
    z ∈ spectrum ℂ (c • M) ↔ z * c⁻¹ ∈ spectrum ℂ M := by
  have hmem : (Units.mk0 c hc : ℂˣ) • (z * c⁻¹) = z := by
    show c * (z * c⁻¹) = z
    field_simp
  have hop : (Units.mk0 c hc : ℂˣ) • M = c • M := rfl
  have key := spectrum.smul_mem_smul_iff (R := ℂ) (a := M) (s := z * c⁻¹)
    (r := Units.mk0 c hc)
  constructor
  · intro h
    refine key.mp ?_
    rw [hmem, hop]
    exact h
  · intro h
    have h' := key.mpr h
    rwa [hmem, hop] at h'

/-- The suspension at coupling `λ` is unitarily equivalent (up to the factor `λ`) to the
suspension at coupling `λ⁻¹`. -/
theorem suspA_smul_conj (α lam : ℝ) (hlam : lam ≠ 0) :
    suspA α lam = (lam : ℂ) • (twistUinv α * suspA α lam⁻¹ * twistU α) := by
  obtain ⟨h1, h2⟩ := twistU_mul α
  have hinter := twistU_intertwines α lam hlam
  calc suspA α lam = twistUinv α * (twistU α * suspA α lam) := by rw [← mul_assoc, h2, one_mul]
    _ = twistUinv α * ((lam : ℂ) • (suspA α lam⁻¹ * twistU α)) := by rw [hinter]
    _ = (lam : ℂ) • (twistUinv α * (suspA α lam⁻¹ * twistU α)) := by rw [mul_smul_comm]
    _ = (lam : ℂ) • (twistUinv α * suspA α lam⁻¹ * twistU α) := by rw [mul_assoc]

theorem spectrum_suspA_smul (α lam : ℝ) (hlam : lam ≠ 0) :
    spectrum ℂ (suspA α lam) = (lam : ℂ) • spectrum ℂ (suspA α lam⁻¹) := by
  obtain ⟨h1, h2⟩ := twistU_mul α
  have hc : (lam : ℂ) ≠ 0 := by exact_mod_cast hlam
  rw [suspA_smul_conj α lam hlam]
  have hconj : spectrum ℂ (twistUinv α * suspA α lam⁻¹ * twistU α)
      = spectrum ℂ (suspA α lam⁻¹) := by
    have h := spectrum.units_conjugate' (R := ℂ) (a := suspA α lam⁻¹)
      (u := (⟨twistU α, twistUinv α, h1, h2⟩ : (EllTwo2 →L[ℂ] EllTwo2)ˣ))
    simpa using h
  have h1' := spectrum.unit_smul_eq_smul (R := ℂ)
    (twistUinv α * suspA α lam⁻¹ * twistU α) (Units.mk0 (lam : ℂ) hc)
  have h2' : spectrum ℂ ((lam : ℂ) • (twistUinv α * suspA α lam⁻¹ * twistU α))
      = (lam : ℂ) • spectrum ℂ (twistUinv α * suspA α lam⁻¹ * twistU α) := h1'
  rw [h2', hconj]

/-- Two-sided Aubry duality for the suspension. -/
theorem mem_spectrum_suspA_iff (α lam : ℝ) (hlam : lam ≠ 0) (E : ℝ) :
    (E : ℂ) ∈ spectrum ℂ (suspA α lam) ↔
      ((E / lam : ℝ) : ℂ) ∈ spectrum ℂ (suspA α lam⁻¹) := by
  obtain ⟨h1, h2⟩ := twistU_mul α
  have hc : (lam : ℂ) ≠ 0 := by exact_mod_cast hlam
  have hconj : spectrum ℂ (twistUinv α * suspA α lam⁻¹ * twistU α)
      = spectrum ℂ (suspA α lam⁻¹) := by
    have h := spectrum.units_conjugate' (R := ℂ) (a := suspA α lam⁻¹)
      (u := (⟨twistU α, twistUinv α, h1, h2⟩ : (EllTwo2 →L[ℂ] EllTwo2)ˣ))
    simpa using h
  rw [suspA_smul_conj α lam hlam, smul_mem_spectrum_iff (lam : ℂ) hc]
  have hdiv : (E : ℂ) * (lam : ℂ)⁻¹ = ((E / lam : ℝ) : ℂ) := by
    push_cast
    field_simp
  rw [hdiv, hconj]

end Work.TMComp.Duality
