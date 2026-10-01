import Mathlib
import Submission.Work.LinnikAreas.Setup
import Submission.Work.LinnikAreas.FamilyZeroCountNonPrincipal
import Submission.Work.LinnikAreas.PrincipalZeroCount
import Submission.Work.LinnikAreas.FamilyZeroCountArith

open DirichletCharacter Complex
open scoped Classical BigOperators

namespace Work.LinnikAreas

/-- **The trivial ("σ-blind") family zero count.**

For every `ε > 0` there is `C > 0` such that, for every `q ≥ 2`, every `σ ∈ [0,1]` and every
`T ≥ 1`, the total number of zeros (with multiplicity) of the completed L-functions of *all*
Dirichlet characters mod `q` in the rectangle `σ ≤ Re ρ ≤ 1`, `|Im ρ| ≤ T` is at most
`C·(qT)^(1+ε)`.

This is the elementary counterpart of `FamilyZeroDensityHyp`: the count is `≪ q·T·log(qT)`
uniformly, by `FamilyZeroCountNonPrincipal` for the non-principal characters and
`PrincipalZeroCount` for the principal one, and the logarithmic factor is absorbed into the
extra power `(qT)^ε` via `FamilyZeroCountArith`. -/
theorem FamilyZeroCountTrivial : ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧
    ∀ q : ℕ, 2 ≤ q → ∀ [NeZero q] (σ T : ℝ), 0 ≤ σ → σ ≤ 1 → 1 ≤ T →
      (Finset.univ.sum (fun χ : DirichletCharacter ℂ q => Work.LinnikAreas.zeroCountIn χ σ T))
        ≤ C * ((q : ℝ) * T) ^ (1 + ε) := by
  intro ε hε
  obtain ⟨C₀, hC₀pos, hC₀⟩ := FamilyZeroCountArith ε hε
  obtain ⟨c₁, hc₁pos, hc₁⟩ := PrincipalZeroCount
  obtain ⟨c₂, hc₂pos, hc₂⟩ := FamilyZeroCountNonPrincipal
  refine ⟨(c₁ + c₂) * C₀, by positivity, ?_⟩
  intro q hq hqne σ T hσ0 hσ1 hT
  -- split the sum over the family into the non-principal characters and the principal one
  have hsplit : Finset.univ.sum (fun χ : DirichletCharacter ℂ q => zeroCountIn χ σ T)
      = (∑ χ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ q), zeroCountIn χ σ T)
        + zeroCountIn (1 : DirichletCharacter ℂ q) σ T :=
    (Finset.sum_erase_add Finset.univ
      (fun χ : DirichletCharacter ℂ q => zeroCountIn χ σ T) (Finset.mem_univ 1)).symm
  have hna := hc₂ q hq σ T hσ0 hσ1 hT
  have hp := hc₁ q hq σ T hσ0 hσ1 hT
  have hsum_le : Finset.univ.sum (fun χ : DirichletCharacter ℂ q => zeroCountIn χ σ T)
      ≤ c₂ * (q:ℝ) * (T+2) * (Real.log ((q:ℝ)*(T+2)) + 2)
        + c₁ * (T+2) * (Real.log ((q:ℝ)*(T+2)) + 2) := by
    rw [hsplit]; exact add_le_add hna hp
  have hq2 : (2:ℝ) ≤ (q:ℝ) := by exact_mod_cast hq
  have hK : 0 ≤ (T + 2) * (Real.log ((q:ℝ)*(T+2)) + 2) := by
    have hT1 : (0:ℝ) < T + 2 := by linarith
    have hone : (1:ℝ) ≤ (q:ℝ) * (T + 2) := by nlinarith
    have hlog0 : 0 ≤ Real.log ((q:ℝ) * (T + 2)) := Real.log_nonneg hone
    positivity
  have hLE : (c₂ * (q:ℝ) + c₁) * ((T+2) * (Real.log ((q:ℝ)*(T+2)) + 2))
      ≤ (c₁ + c₂) * ((q:ℝ) * (T+2) * (Real.log ((q:ℝ)*(T+2)) + 2)) := by
    have hcoef : c₂ * (q:ℝ) + c₁ ≤ (c₁ + c₂) * (q:ℝ) := by nlinarith [hc₁pos, hq2]
    calc (c₂ * (q:ℝ) + c₁) * ((T+2) * (Real.log ((q:ℝ)*(T+2)) + 2))
        ≤ ((c₁ + c₂) * (q:ℝ)) * ((T+2) * (Real.log ((q:ℝ)*(T+2)) + 2)) :=
          mul_le_mul_of_nonneg_right hcoef hK
      _ = (c₁ + c₂) * ((q:ℝ) * (T+2) * (Real.log ((q:ℝ)*(T+2)) + 2)) := by ring
  have hbound2 : c₂ * (q:ℝ) * (T+2) * (Real.log ((q:ℝ)*(T+2)) + 2)
      + c₁ * (T+2) * (Real.log ((q:ℝ)*(T+2)) + 2)
      ≤ (c₁ + c₂) * ((q:ℝ) * (T+2) * (Real.log ((q:ℝ)*(T+2)) + 2)) := by
    have heq : c₂ * (q:ℝ) * (T+2) * (Real.log ((q:ℝ)*(T+2)) + 2)
        + c₁ * (T+2) * (Real.log ((q:ℝ)*(T+2)) + 2)
        = (c₂ * (q:ℝ) + c₁) * ((T+2) * (Real.log ((q:ℝ)*(T+2)) + 2)) := by ring
    rw [heq]; exact hLE
  have hstep3 : (c₁ + c₂) * ((q:ℝ) * (T+2) * (Real.log ((q:ℝ)*(T+2)) + 2))
      ≤ (c₁ + c₂) * (C₀ * ((q:ℝ)*T)^(1+ε)) :=
    mul_le_mul_of_nonneg_left (hC₀ q hq T hT) (by positivity)
  calc Finset.univ.sum (fun χ : DirichletCharacter ℂ q => zeroCountIn χ σ T)
      ≤ c₂ * (q:ℝ) * (T+2) * (Real.log ((q:ℝ)*(T+2)) + 2)
        + c₁ * (T+2) * (Real.log ((q:ℝ)*(T+2)) + 2) := hsum_le
    _ ≤ (c₁ + c₂) * ((q:ℝ) * (T+2) * (Real.log ((q:ℝ)*(T+2)) + 2)) := hbound2
    _ ≤ (c₁ + c₂) * (C₀ * ((q:ℝ)*T)^(1+ε)) := hstep3
    _ = ((c₁ + c₂) * C₀) * ((q:ℝ)*T)^(1+ε) := by ring

end Work.LinnikAreas
