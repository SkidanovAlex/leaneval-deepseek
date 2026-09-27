import Mathlib
import Submission.Work.EQ.Defs

namespace Work.EQ

open Complex

/-- **Periodicity and the sum relation for a symmetric normalised equichordal curve.**

From `NormEqCurve` alone the two chord identities `ρᵢ θ + ρᵢ (θ+π) = 1` (`i = 1, 2`) give,
by shifting the second variable by `π` and subtracting, `ρᵢ (θ+2π) = ρᵢ θ`.  The symmetry
hypotheses `hs₁` (evenness of `ρ₁`) and `hs₂` (`ρ₂ θ = ρ₁ (π-θ)`) give the sum relation:
`ρ₂ θ = ρ₁ (π-θ)` while `ρ₂ (θ+π) = ρ₁ (π-(θ+π)) = ρ₁ (-θ) = ρ₁ θ`, so
`1 = ρ₂ θ + ρ₂ (θ+π) = ρ₁ (π-θ) + ρ₁ θ`. -/
theorem normEqCurve_periodic_and_sum {a : ℝ} {ρ₁ ρ₂ : ℝ → ℝ} (hC : NormEqCurve a ρ₁ ρ₂)
    (hs₁ : ∀ θ, ρ₁ (-θ) = ρ₁ θ) (hs₂ : ∀ θ, ρ₂ θ = ρ₁ (Real.pi - θ)) :
    Function.Periodic ρ₁ (2 * Real.pi) ∧ Function.Periodic ρ₂ (2 * Real.pi) ∧
      (∀ θ, ρ₂ θ = 1 - ρ₁ θ) := by
  obtain ⟨-, -, -, -, h₁, h₂, -⟩ := hC
  refine ⟨?_, ?_, ?_⟩
  · intro θ
    have h := h₁ θ
    have h' := h₁ (θ + Real.pi)
    have harg : θ + 2 * Real.pi = θ + Real.pi + Real.pi := by ring
    rw [harg]
    linarith
  · intro θ
    have h := h₂ θ
    have h' := h₂ (θ + Real.pi)
    have harg : θ + 2 * Real.pi = θ + Real.pi + Real.pi := by ring
    rw [harg]
    linarith
  · intro θ
    have h2 := h₂ θ
    have hπ : ρ₁ (Real.pi - (θ + Real.pi)) = ρ₁ (-θ) := by congr 1; ring
    rw [hs₂ θ, hs₂ (θ + Real.pi), hπ, hs₁ θ] at h2
    rw [hs₂ θ]
    linarith

end Work.EQ
