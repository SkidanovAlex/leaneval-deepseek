import Mathlib
import Submission.Work.BMF.Defs
import Submission.Work.BMF.adi_const
import Submission.Work.N8.poly_le_exp
import Submission.Work.N8.exp_le_rpow_ceil_pi0
import Submission.Work.N8.lhs_pow_bound

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# `Work.N8.scale_qe_ineq7`

Final scale inequality of the MRT T Z pipeline: for large `X`, the power of
`(2 P₁)^{2ℓ+2} · X/(P₁P₂)` with exponent `max (Kc k) 1` is dominated by
`(P₂/2)^{⌈c π₀(P₂)⌉}`.  The right-hand side grows like `exp(c P₂ / 2)` while the
left-hand side is a fixed polynomial in `X` of degree `max (Kc k) 1 · (1 + ε(2ℓ+2))`,
and `P₂ ≥ X^{ε²/2}`, so exponential beats polynomial.
-/

namespace Work.N8

theorem scale_qe_ineq7 (k : ℕ) (θ ε c : ℝ) (ℓ : ℕ)
    (hθ₀ : 0 < θ) (hθ₁ : θ < 1 / 2) (hε : 0 < ε) (hεθ : ε ≤ θ / 100) (hc : 0 < c) :
    ∃ N : ℝ, ∀ X H P₁ P₂ : ℝ, N ≤ X → X ^ θ ≤ H → H ≤ X ^ (1 - θ) →
      X ^ (ε ^ 2 / 2) ≤ P₁ → P₁ ≤ X ^ ε → X ^ (ε ^ 2 / 2) ≤ P₂ → P₂ ≤ X ^ ε →
      ((2 * P₁) ^ (2 * ℓ + 2) * (X / (P₁ * P₂))) ^ (max (Work.BMF.Kc k) 1)
        ≤ (P₂ / 2) ^ ⌈c * Work.BMF.pi0 P₂⌉₊ := by
  have hs : (0 : ℝ) < ε ^ 2 / 2 := by positivity
  have hη : (0 : ℝ) < c / 2 := by positivity
  obtain ⟨N₁, hN₁1, hN₁⟩ :=
    poly_le_exp ((2 : ℝ) ^ ((2 * ℓ + 2) * max (Work.BMF.Kc k) 1))
      ((ε * (2 * ℓ + 2 : ℕ) + 1 - ε ^ 2) * (max (Work.BMF.Kc k) 1 : ℝ))
      (c / 2) (ε ^ 2 / 2) (by positivity) hη hs
  refine ⟨max N₁ (4 ^ (2 / ε ^ 2) + 1), ?_⟩
  intro X H P₁ P₂ hX hH1 hH2 hP1lo hP1hi hP2lo hP2hi
  have hXN₁ : N₁ ≤ X := le_trans (le_max_left _ _) hX
  have hX1 : (1 : ℝ) ≤ X := le_trans (le_trans hN₁1 (le_max_left _ _)) hX
  have hX4 : (4 : ℝ) ^ (2 / ε ^ 2) ≤ X :=
    le_trans (le_trans (by linarith : (4 : ℝ) ^ (2 / ε ^ 2) ≤ 4 ^ (2 / ε ^ 2) + 1)
      (le_max_right _ _)) hX
  have hx : (4 : ℝ) ≤ X ^ (ε ^ 2 / 2) := by
    have h1 : ((4 : ℝ) ^ (2 / ε ^ 2)) ^ (ε ^ 2 / 2) ≤ X ^ (ε ^ 2 / 2) :=
      Real.rpow_le_rpow (by positivity) hX4 (by positivity)
    have hmul : (2 / ε ^ 2) * (ε ^ 2 / 2) = 1 := by field_simp
    rwa [← Real.rpow_mul (show (0 : ℝ) ≤ 4 by norm_num) (2 / ε ^ 2) (ε ^ 2 / 2), hmul,
      Real.rpow_one] at h1
  calc ((2 * P₁) ^ (2 * ℓ + 2) * (X / (P₁ * P₂))) ^ (max (Work.BMF.Kc k) 1)
      ≤ (2 : ℝ) ^ ((2 * ℓ + 2) * max (Work.BMF.Kc k) 1)
          * X ^ ((ε * (2 * ℓ + 2 : ℕ) + 1 - ε ^ 2) * (max (Work.BMF.Kc k) 1 : ℝ)) :=
        lhs_pow_bound k ℓ ε X P₁ P₂ hε hX1 hP1lo hP1hi hP2lo
    _ ≤ Real.exp (c / 2 * X ^ (ε ^ 2 / 2)) := hN₁ X hXN₁
    _ ≤ (P₂ / 2) ^ ⌈c * Work.BMF.pi0 P₂⌉₊ :=
        exp_le_rpow_ceil_pi0 c (X ^ (ε ^ 2 / 2)) P₂ hc hx hP2lo

end Work.N8
