import Mathlib
import Submission.Work.EKLC8Core.Vol
import Submission.Work.EKLC8Core.aDiag_add

namespace Work.EKLC8Core

/-- The diagonal element `aDiag` is the identity at the zero exponent. -/
theorem aDiag_zero : aDiag (0 : Fin 3 → ℝ) = 1 := by
  apply Subtype.ext
  simp [aDiag]

/-- `φ_0 = 1`: the contracting flow starts at the identity. -/
theorem phi_zero : phi 0 = 1 := by
  rw [phi, zero_smul, aDiag_zero]

/-- `φ_{τ+σ} = φ_τ φ_σ`: `φ` is a one-parameter subgroup, i.e. a group homomorphism
`(ℝ, +) → SL₃(ℝ)`. -/
theorem phi_add (τ σ : ℝ) : phi (τ + σ) = phi τ * phi σ := by
  rw [phi, phi, phi, add_smul, aDiag_add]

/-- `φ_τ⁻¹ = φ_{-τ}`. -/
theorem phi_inv (τ : ℝ) : (phi τ)⁻¹ = phi (-τ) := by
  have h : phi τ * phi (-τ) = 1 := by
    rw [← phi_add, add_neg_cancel, phi_zero]
  exact inv_eq_of_mul_eq_one_right h

theorem phi_alg :
    (phi 0 = 1) ∧ (∀ τ σ : ℝ, phi (τ + σ) = phi τ * phi σ) ∧
    (∀ τ : ℝ, (phi τ)⁻¹ = phi (-τ)) :=
  ⟨phi_zero, phi_add, phi_inv⟩

end Work.EKLC8Core
