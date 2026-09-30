import Mathlib
import Submission.Work.BMF.Defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.N8

theorem window_bounds (θ ε X P₁ P₂ : ℝ) (hθ₁ : θ < 1 / 2) (hε : 0 < ε) (hεθ : ε ≤ θ / 100)
    (hX1 : 1 ≤ X) (hL1 : 1 ≤ Real.log X) (hLle : Real.log X ≤ X ^ (ε ^ 2 / 2))
    (hy3 : 3 ≤ X ^ (ε ^ 2 / 2))
    (hP₁1 : X ^ (ε ^ 2 / 2) ≤ P₁) (hP₁2 : P₁ ≤ X ^ ε)
    (hP₂1 : X ^ (ε ^ 2 / 2) ≤ P₂) (hP₂2 : P₂ ≤ X ^ ε) :
    P₁ ≤ X ∧ 1 < P₁ ∧ Real.log P₁ ≤ Real.log X ∧ P₁ * P₂ ≤ X ∧
      1 ≤ X / (P₁ * P₂) ∧ X / (P₁ * P₂) ≤ X ∧ 0 ≤ Real.log (X / (P₁ * P₂)) ∧
      Real.log (X / (P₁ * P₂)) ≤ Real.log X ∧
      X ^ (ε ^ 2 / 2) / Real.log X ≤ Work.BMF.pi0 P₁ ∧
      1 ≤ X ^ (ε ^ 2 / 2) / Real.log X := by
  have hX0 : (0 : ℝ) < X := by linarith
  have hε1 : ε ≤ 1 := by linarith
  have h2ε : 2 * ε ≤ 1 := by linarith
  have hP₁gt1 : 1 < P₁ := by linarith
  have hP₁pos : 0 < P₁ := by linarith
  have hP₁ge1 : 1 ≤ P₁ := by linarith
  have hP₂pos : 0 < P₂ := by linarith
  have hP₂ge1 : 1 ≤ P₂ := by linarith
  have hlogXpos : 0 < Real.log X := by linarith
  have hXεpos : 0 < X ^ ε := Real.rpow_pos_of_pos hX0 ε
  have hXε_le_X : X ^ ε ≤ X := by
    simpa using Real.rpow_le_rpow_of_exponent_le hX1 hε1
  have hP₁_le_X : P₁ ≤ X := le_trans hP₁2 hXε_le_X
  have hlogP₁_le_logX : Real.log P₁ ≤ Real.log X := Real.log_le_log hP₁pos hP₁_le_X
  have hlogP₁pos : 0 < Real.log P₁ := Real.log_pos hP₁gt1
  have hX2ε : X ^ ε * X ^ ε ≤ X := by
    have h1 : X ^ ε * X ^ ε = X ^ (ε + ε) := (Real.rpow_add hX0 ε ε).symm
    rw [h1, show ε + ε = 2 * ε by ring]
    simpa using Real.rpow_le_rpow_of_exponent_le hX1 h2ε
  have hP₁P₂_le : P₁ * P₂ ≤ X :=
    le_trans (mul_le_mul hP₁2 hP₂2 (le_of_lt hP₂pos) (le_of_lt hXεpos)) hX2ε
  have hP₁P₂pos : 0 < P₁ * P₂ := mul_pos hP₁pos hP₂pos
  have hP₁P₂ge1 : 1 ≤ P₁ * P₂ := by nlinarith
  have hdiv1 : 1 ≤ X / (P₁ * P₂) := by
    rw [one_le_div hP₁P₂pos]
    exact hP₁P₂_le
  have hdiv_le : X / (P₁ * P₂) ≤ X := by
    rw [div_le_iff₀ hP₁P₂pos]
    nlinarith
  have hdivpos : 0 < X / (P₁ * P₂) := by linarith
  refine ⟨hP₁_le_X, hP₁gt1, hlogP₁_le_logX, hP₁P₂_le, hdiv1, hdiv_le, ?_, ?_, ?_, ?_⟩
  · exact Real.log_nonneg hdiv1
  · exact Real.log_le_log hdivpos hdiv_le
  · rw [Work.BMF.pi0, div_le_iff₀ hlogXpos]
    have hrw : P₁ / Real.log P₁ * Real.log X = P₁ * Real.log X / Real.log P₁ := by ring
    rw [hrw, le_div_iff₀ hlogP₁pos]
    exact mul_le_mul hP₁1 hlogP₁_le_logX (le_of_lt hlogP₁pos) (le_of_lt hP₁pos)
  · rw [one_le_div hlogXpos]
    exact hLle

end Work.N8
