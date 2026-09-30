import Mathlib
import Submission.Work.BMF.Defs
import Submission.Work.N8.scales_large

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.N8

theorem scale_c0 (θ ε c₀ : ℝ) (hθ₀ : 0 < θ) (hθ₁ : θ < 1 / 2) (hε : 0 < ε)
    (hεθ : ε ≤ θ / 100) (hc₀ : 0 < c₀) (hc₀θ : c₀ ≤ θ / 2) (hc₀ε : c₀ ≤ ε ^ 2 / 2) :
    ∃ X₀ : ℝ, ∀ X H P₁ P₂ : ℝ, X₀ ≤ X → X ^ θ ≤ H → H ≤ X ^ (1 - θ) →
      X ^ (ε ^ 2 / 2) ≤ P₁ → P₁ ≤ X ^ ε → X ^ (ε ^ 2 / 2) ≤ P₂ → P₂ ≤ X ^ ε →
      (X / (P₁ * P₂)) ^ c₀ ≤ P₁ ∧ P₁ ≤ (X / (P₁ * P₂)) ^ (1 / 4 : ℝ) ∧
      (X / (P₁ * P₂)) ^ c₀ ≤ H / (P₁ * P₂) ∧ H / (P₁ * P₂) ≤ X / (P₁ * P₂) := by
  obtain ⟨C, hCpos, hC⟩ := scales_large θ ε hθ₀ hθ₁ hε hεθ
  refine ⟨C, fun X H P₁ P₂ hCX hHlo hHhi hP1lo hP1hi hP2lo hP2hi => ?_⟩
  obtain ⟨hXpos, hX1, hHpos, hP1pos, hP1one, hP2pos, hP2four, hP1P2pos, hP1P210,
      hlogX, hApos, hA10, hA1, hAlo, hAhi, hA_half, hA_10le, hXHpos, hXH3, hXHle,
      hBpos, hB1, hBlo, hB_theta2, hBhi, hBle, hAhalf2, hlogP1, hlogP1one, hlogP2,
      hlogP22, hpi0⟩ := hC X H P₁ P₂ hCX hHlo hHhi hP1lo hP1hi hP2lo hP2hi
  -- elementary exponent inequalities
  have h_eps_quarter : ε ≤ (1 - 2 * ε) / 4 := by nlinarith [hεθ, hθ₁, hε]
  have h_c0_theta : c₀ ≤ θ - 2 * ε := by nlinarith [hc₀θ, hεθ, hθ₀]
  refine ⟨?_, ?_, ?_, hBhi⟩
  · -- (X/(P₁P₂))^c₀ ≤ P₁
    calc (X / (P₁ * P₂)) ^ c₀ ≤ X ^ c₀ := Real.rpow_le_rpow hApos.le hAhi hc₀.le
      _ ≤ X ^ (ε ^ 2 / 2) := Real.rpow_le_rpow_of_exponent_le hX1 hc₀ε
      _ ≤ P₁ := hP1lo
  · -- P₁ ≤ (X/(P₁P₂))^(1/4)
    calc P₁ ≤ X ^ ε := hP1hi
      _ ≤ X ^ ((1 - 2 * ε) / 4) := Real.rpow_le_rpow_of_exponent_le hX1 h_eps_quarter
      _ = (X ^ (1 - 2 * ε)) ^ (1 / 4 : ℝ) := by
            rw [← Real.rpow_mul hXpos.le]; ring_nf
      _ ≤ (X / (P₁ * P₂)) ^ (1 / 4 : ℝ) :=
            Real.rpow_le_rpow (Real.rpow_nonneg hXpos.le _) hAlo (by norm_num)
  · -- (X/(P₁P₂))^c₀ ≤ H/(P₁P₂)
    calc (X / (P₁ * P₂)) ^ c₀ ≤ X ^ c₀ := Real.rpow_le_rpow hApos.le hAhi hc₀.le
      _ ≤ X ^ (θ - 2 * ε) := Real.rpow_le_rpow_of_exponent_le hX1 h_c0_theta
      _ ≤ H / (P₁ * P₂) := hBlo

end Work.N8
