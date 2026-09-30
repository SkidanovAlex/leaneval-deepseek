import Mathlib
import Submission.Work.BMF.Defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option linter.unusedVariables false

namespace Work.N8

/-- Quantitative separation of an "edge" term: for `X` large, the expression
`800 * (H / (P₁ * P₂)) * P₁ ^ 2` is dominated by `X / (P₁ * P₂) / 10`, uniformly over all
admissible `H, P₁, P₂`.

The point is that `H ≤ X ^ (1 - θ)` and `P₁ ≤ X ^ ε` give
`H * P₁ ^ 2 ≤ X ^ (1 - θ + 2ε)`, while `2ε ≤ θ/50 < θ` makes the exponent `1 - θ + 2ε` strictly
smaller than `1`, so `8000 * X ^ (1 - θ + 2ε) < X` for large `X`. -/
theorem edge_sep_800 (θ ε : ℝ) (hθ₀ : 0 < θ) (hθ₁ : θ < 1 / 2) (hε : 0 < ε)
    (hεθ : ε ≤ θ / 100) :
    ∃ X₀ : ℝ, ∀ X H P₁ P₂ x : ℝ, X₀ ≤ X → X ^ θ ≤ H → H ≤ X ^ (1 - θ) →
      X ^ (ε ^ 2 / 2) ≤ P₁ → P₁ ≤ X ^ ε → X ^ (ε ^ 2 / 2) ≤ P₂ → P₂ ≤ X ^ ε →
      X / (P₁ * P₂) / 10 ≤ x → 800 * (H / (P₁ * P₂)) * P₁ ^ 2 < x := by
  have hθ2 : 2 * ε < θ := by
    have h2 : 2 * ε ≤ 2 * (θ / 100) := by linarith [hεθ]
    linarith [h2, hθ₀]
  have hc : 0 < θ - 2 * ε := by linarith
  have hev : ∀ᶠ X in Filter.atTop, (8000:ℝ) < X ^ (θ - 2 * ε) :=
    (tendsto_rpow_atTop hc).eventually
      (Filter.eventually_atTop.mpr ⟨8000 + 1, fun b hb => by linarith⟩)
  obtain ⟨X₀, hX₀⟩ := Filter.eventually_atTop.mp hev
  refine ⟨max X₀ 1, ?_⟩
  intro X H P₁ P₂ x hX hXθ hH hP1lo hP1hi hP2lo hP2hi hx
  have hX1 : (1:ℝ) ≤ X := le_trans (le_max_right _ _) hX
  have hX₀' : X₀ ≤ X := le_trans (le_max_left _ _) hX
  have hXpos : 0 < X := lt_of_lt_of_le zero_lt_one hX1
  have hgt : (8000:ℝ) < X ^ (θ - 2 * ε) := hX₀ X hX₀'
  have hP1pos : 0 < P₁ := lt_of_lt_of_le (Real.rpow_pos_of_pos hXpos _) hP1lo
  have hP2pos : 0 < P₂ := lt_of_lt_of_le (Real.rpow_pos_of_pos hXpos _) hP2lo
  have hHpos : 0 < H := lt_of_lt_of_le (Real.rpow_pos_of_pos hXpos θ) hXθ
  have hP1sq : P₁ ^ 2 ≤ X ^ (2 * ε) := by
    have h := mul_self_le_mul_self (le_of_lt hP1pos) hP1hi
    rw [sq]
    calc P₁ * P₁ ≤ X ^ ε * X ^ ε := h
      _ = X ^ (2 * ε) := by rw [← Real.rpow_add hXpos]; congr 1; ring
  have hHP : H * P₁ ^ 2 ≤ X ^ (1 - θ) * X ^ (2 * ε) :=
    mul_le_mul hH hP1sq (by positivity) (Real.rpow_nonneg (le_of_lt hXpos) _)
  have hexp2 : X ^ (1 - θ) * X ^ (2 * ε) = X ^ (1 - (θ - 2 * ε)) := by
    rw [← Real.rpow_add hXpos]
    congr 1
    ring
  have hHP2 : H * P₁ ^ 2 ≤ X ^ (1 - (θ - 2 * ε)) := hHP.trans (le_of_eq hexp2)
  have h2 : 8000 * X ^ (1 - (θ - 2 * ε)) < X := by
    have h := mul_lt_mul_of_pos_right hgt (Real.rpow_pos_of_pos hXpos (1 - (θ - 2 * ε)))
    rwa [← Real.rpow_add hXpos, show (θ - 2 * ε) + (1 - (θ - 2 * ε)) = 1 by ring,
      Real.rpow_one] at h
  have hbig : 8000 * (H * P₁ ^ 2) < X := by
    have hle : 8000 * (H * P₁ ^ 2) ≤ 8000 * X ^ (1 - (θ - 2 * ε)) :=
      mul_le_mul_of_nonneg_left hHP2 (by norm_num)
    linarith [hle, h2]
  have h1 : 800 * (H * P₁ ^ 2) < X / 10 := by linarith [hbig]
  have hP1P2pos : 0 < P₁ * P₂ := mul_pos hP1pos hP2pos
  have hmain : 800 * (H / (P₁ * P₂)) * P₁ ^ 2 < X / (P₁ * P₂) / 10 := by
    have heq : 800 * (H / (P₁ * P₂)) * P₁ ^ 2 = 800 * (H * P₁ ^ 2) / (P₁ * P₂) := by
      field_simp
    rw [heq]
    calc 800 * (H * P₁ ^ 2) / (P₁ * P₂) < (X / 10) / (P₁ * P₂) :=
            div_lt_div_of_pos_right h1 hP1P2pos
      _ = X / (P₁ * P₂) / 10 := by rw [div_div, div_div]; ring
  linarith [hmain, hx]

end Work.N8
