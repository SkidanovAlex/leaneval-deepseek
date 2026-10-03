import Mathlib
import Submission.Work.A3Fix.PolyEnergyBoundOfDeep
import Submission.Work.A3.deepArc_largeDenominator
import Submission.Work.A3.deepArc_smallDenominator

set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace Work.A3

open MeasureTheory Polynomial Finset
open scoped ENNReal NNReal BigOperators

noncomputable section

/-- **The deep-shoulder power saving `(DEEP'')`**, obtained by combining its two halves:
the large-denominator half (`deepArc_largeDenominator`, Weyl's inequality) and the
small-denominator half (`deepArc_smallDenominator`, residue split + the Fresnel/van der Corput
bound on the block sums). -/
theorem deepBound (Q : Polynomial ℤ) (hd : 2 ≤ Polynomial.natDegree Q)
    {ε₀ : ℝ} (hε₀ : 0 < ε₀) (hε₀1 : ε₀ ≤ 1 / 2) :
    ∃ C₀ θ₀ : ℝ, 0 < θ₀ ∧ 0 < C₀ ∧
      ∀ (N : ℕ) (a q : ℤ) (β : ℝ), 1 ≤ N → 1 ≤ q → IsCoprime a (q : ℤ) →
        (q : ℝ) ≤ (N : ℝ) ^ (1 / 2 : ℝ) →
        ((N : ℝ) / (q : ℝ)) ^ ((Q.natDegree : ℝ) / (Q.natDegree + 1)) / 100
          ≤ |β| * (N : ℝ) ^ Q.natDegree →
        |β| ≤ 1 / ((q : ℝ) * (N : ℝ) ^ ((Q.natDegree : ℝ) / 2)) →
        ‖expSum Q N ((a : ℝ) / (q : ℝ) + β)‖ ≤ C₀ * (N : ℝ) ^ (1 - θ₀) := by
  obtain ⟨C₁, θ₁, hθ₁, hC₁, h₁⟩ := deepArc_largeDenominator Q hd hε₀ hε₀1
  obtain ⟨C₂, θ₂, hθ₂, hC₂, h₂⟩ := deepArc_smallDenominator Q hd hε₀ hε₀1
  refine ⟨max C₁ C₂, min θ₁ θ₂, lt_min hθ₁ hθ₂, lt_max_of_lt_left hC₁, ?_⟩
  intro N a q β hN hq hcop hqhalf hβlow hβhigh
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hC₁le : C₁ ≤ max C₁ C₂ := le_max_left _ _
  have hC₂le : C₂ ≤ max C₁ C₂ := le_max_right _ _
  have hθ₁le : min θ₁ θ₂ ≤ θ₁ := min_le_left _ _
  have hθ₂le : min θ₁ θ₂ ≤ θ₂ := min_le_right _ _
  have hpow₁ : (N : ℝ) ^ (1 - θ₁) ≤ (N : ℝ) ^ (1 - min θ₁ θ₂) :=
    Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
  have hpow₂ : (N : ℝ) ^ (1 - θ₂) ≤ (N : ℝ) ^ (1 - min θ₁ θ₂) :=
    Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
  by_cases hcase : (N : ℝ) ^ ε₀ ≤ (q : ℝ)
  · calc ‖expSum Q N ((a : ℝ) / (q : ℝ) + β)‖ ≤ C₁ * (N : ℝ) ^ (1 - θ₁) :=
          h₁ N a q β hN hq hcop hcase hqhalf hβhigh
      _ ≤ max C₁ C₂ * (N : ℝ) ^ (1 - min θ₁ θ₂) := by
          refine mul_le_mul hC₁le hpow₁ (by positivity) (by positivity)
  · have hqε : (q : ℝ) ≤ (N : ℝ) ^ ε₀ := le_of_lt (not_le.mp hcase)
    calc ‖expSum Q N ((a : ℝ) / (q : ℝ) + β)‖ ≤ C₂ * (N : ℝ) ^ (1 - θ₂) :=
          h₂ N a q β hN hq hcop hqε hqhalf hβlow hβhigh
      _ ≤ max C₁ C₂ * (N : ℝ) ^ (1 - min θ₁ θ₂) := by
          refine mul_le_mul hC₂le hpow₂ (by positivity) (by positivity)

/-- **The arithmetic core of Area A3**, unconditional. -/
theorem polyEnergy_bound_complete (Q : Polynomial ℤ) (hd : 2 ≤ Polynomial.natDegree Q) :
    PolyEnergyBound Q := by
  obtain ⟨C₀, θ₀, hθ₀, hC₀, hdeep⟩ :=
    deepBound Q hd (ε₀ := 1 / 4) (by norm_num) (by norm_num)
  exact polyEnergy_bound_of_deep Q hd hθ₀ hC₀ hdeep

end

end Work.A3
