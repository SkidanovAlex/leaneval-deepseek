import Mathlib
import Submission.Work.BMF.Defs
import Submission.Work.BMF.adi_const
import Submission.Work.N8.qe6_ratio_atTop
import Submission.Work.N8.qe6_num
import Submission.Work.N8.qe6_pi0_lower
import Submission.Work.N8.qe6_den

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.N8

open Filter

/-- **Step `qe6` of the scale comparison.**

For every `k, θ, ε, c, ℓ, δ` with `0 < θ < 1/2`, `0 < ε ≤ θ/100`, `0 < c`,
`0 < δ ≤ 1` and `2δ ≤ c` there is `N` such that for all `X ≥ N` and all
`P₁, P₂ ∈ [X^{ε²/2}, X^ε]` (and any `H` in the admissible window) one has
`K₀(k) · (polylog numerator) / log(P₂/2) ≤ (c - δ) π₀(P₂)`.

This is the "denominator/`π₀` comparison" step of `scale_qe`: the numerator is
`O(log X)` while `log(P₂/2) ≍ log X` and `π₀(P₂) = P₂/log P₂` is as large as
`X^{ε²/2}/(ε log X) → ∞`, so for `X` large the `π₀(P₂)` term dominates. -/
theorem scale_qe_ineq6 (k : ℕ) (θ ε c : ℝ) (ℓ : ℕ) (δ : ℝ)
    (hθ₀ : 0 < θ) (hθ₁ : θ < 1 / 2) (hε : 0 < ε) (hεθ : ε ≤ θ / 100)
    (hc : 0 < c) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hδc : 2 * δ ≤ c) :
    ∃ N : ℝ, ∀ X H P₁ P₂ : ℝ, N ≤ X → X ^ θ ≤ H → H ≤ X ^ (1 - θ) →
      X ^ (ε ^ 2 / 2) ≤ P₁ → P₁ ≤ X ^ ε → X ^ (ε ^ 2 / 2) ≤ P₂ → P₂ ≤ X ^ ε →
      (Work.BMF.K0c k : ℝ) *
          ((2 * (ℓ : ℝ) + 2) * Real.log (2 * P₁) + Real.log (X / (P₁ * P₂)) + 1)
          / Real.log (P₂ / 2) ≤ (c - δ) * Work.BMF.pi0 P₂ := by
  have hε2 : (0 : ℝ) < ε ^ 2 / 2 := by positivity
  have hcδ : 0 < c - δ := by linarith
  -- The relevant constants: `K = K₀(k)`, `M = 2ℓ+2`, `Ab = M(ε + log 2) + 2`,
  -- `Cs = 4 K Ab / ε²` (the constant bound on the left-hand side) and
  -- `Cl = Cs ε/(c-δ)` (the threshold the ratio `X^{ε²/2}/log X` must exceed).
  let K : ℝ := (Work.BMF.K0c k : ℝ)
  let M : ℝ := 2 * (ℓ : ℝ) + 2
  let Ab : ℝ := M * (ε + Real.log 2) + 2
  let Cs : ℝ := 4 * K * Ab / ε ^ 2
  let Cl : ℝ := Cs * ε / (c - δ)
  have hK0 : 0 ≤ K := by show (0 : ℝ) ≤ (Work.BMF.K0c k : ℝ); positivity
  have hM0 : 0 ≤ M := by show (0 : ℝ) ≤ 2 * (ℓ : ℝ) + 2; positivity
  have hAb0 : 0 ≤ Ab := by
    show (0 : ℝ) ≤ M * (ε + Real.log 2) + 2
    have h2 : 0 ≤ ε + Real.log 2 := by
      have := Real.log_pos (by norm_num : (1 : ℝ) < 2); linarith
    have := mul_nonneg hM0 h2; linarith
  -- All the asymptotic conditions on `X` hold eventually.
  have hE : ∀ᶠ X in Filter.atTop, (1 : ℝ) ≤ X ∧ 1 ≤ Real.log X ∧
      4 * Real.log 2 / ε ^ 2 ≤ Real.log X ∧ Cl ≤ X ^ (ε ^ 2 / 2) / Real.log X ∧
      (4 : ℝ) ≤ X ^ (ε ^ 2 / 2) := by
    filter_upwards [Filter.eventually_ge_atTop (1 : ℝ),
      Real.tendsto_log_atTop.eventually_ge_atTop (1 : ℝ),
      Real.tendsto_log_atTop.eventually_ge_atTop (4 * Real.log 2 / ε ^ 2),
      qe6_ratio_atTop (ε ^ 2 / 2) Cl hε2,
      (tendsto_rpow_atTop hε2).eventually_ge_atTop (4 : ℝ)] with X hX1 hlog1 hlog2 hbig hr4
    exact ⟨hX1, hlog1, hlog2, hbig, hr4⟩
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp hE
  refine ⟨N, fun X H P₁ P₂ hNX _ _ hP1l hP1u hP2l hP2u => ?_⟩
  obtain ⟨hX1, hlog1, hlog2, hbig, hr4⟩ := hN X hNX
  have hXpos : 0 < X := by linarith
  have hlogXpos : 0 < Real.log X := by linarith
  change K * (M * Real.log (2 * P₁) + Real.log (X / (P₁ * P₂)) + 1) / Real.log (P₂ / 2)
      ≤ (c - δ) * Work.BMF.pi0 P₂
  have hn : M * Real.log (2 * P₁) + Real.log (X / (P₁ * P₂)) + 1 ≤ Ab * Real.log X :=
    qe6_num ℓ ε X P₁ P₂ hε hX1 hlog1 hP1l hP1u hP2l hr4
  have hd : ε ^ 2 / 4 * Real.log X ≤ Real.log (P₂ / 2) :=
    qe6_den ε X P₂ hε hXpos hlog2 hP2l hr4
  have hpi : X ^ (ε ^ 2 / 2) / (ε * Real.log X) ≤ Work.BMF.pi0 P₂ :=
    qe6_pi0_lower ε X P₂ hε hXpos hlog1 hP2l hP2u hr4
  have hdpos : 0 < Real.log (P₂ / 2) := by
    have hP24 : (4 : ℝ) ≤ P₂ := le_trans hr4 hP2l
    exact Real.log_pos (by linarith)
  have hdenpos : 0 < ε ^ 2 / 4 * Real.log X := by
    have : (0 : ℝ) < ε ^ 2 / 4 := by positivity
    exact mul_pos this hlogXpos
  -- Bounding the left-hand side from above by the constant `Cs`.
  have h1 : K * (M * Real.log (2 * P₁) + Real.log (X / (P₁ * P₂)) + 1) / Real.log (P₂ / 2)
      ≤ K * (Ab * Real.log X) / Real.log (P₂ / 2) := by
    apply div_le_div_of_nonneg_right _ (le_of_lt hdpos)
    exact mul_le_mul_of_nonneg_left hn hK0
  have h2 : K * (Ab * Real.log X) / Real.log (P₂ / 2)
      ≤ K * (Ab * Real.log X) / (ε ^ 2 / 4 * Real.log X) := by
    apply div_le_div_of_nonneg_left _ hdenpos hd
    exact mul_nonneg hK0 (mul_nonneg hAb0 (le_of_lt hlogXpos))
  have h3 : K * (Ab * Real.log X) / (ε ^ 2 / 4 * Real.log X) = Cs := by
    show K * (Ab * Real.log X) / (ε ^ 2 / 4 * Real.log X) = 4 * K * Ab / ε ^ 2
    rw [div_eq_iff (by positivity : (ε ^ 2 / 4 * Real.log X) ≠ 0)]
    field_simp
  -- Bounding the right-hand side from below by `Cs`.
  have hCl_eq : (c - δ) * Cl = Cs * ε := by
    show (c - δ) * (Cs * ε / (c - δ)) = Cs * ε
    field_simp
  have h6 : Cs * ε ≤ (c - δ) * X ^ (ε ^ 2 / 2) / Real.log X := by
    have h := mul_le_mul_of_nonneg_left hbig (le_of_lt hcδ)
    rw [hCl_eq, ← mul_div_assoc] at h
    exact h
  have h5 : Cs ≤ (c - δ) * (X ^ (ε ^ 2 / 2) / (ε * Real.log X)) := by
    have h := div_le_div_of_nonneg_right h6 (le_of_lt hε)
    rw [mul_div_cancel_right₀ Cs (ne_of_gt hε)] at h
    rw [div_div, mul_comm (Real.log X) ε] at h
    rwa [← mul_div_assoc]
  have h4 : (c - δ) * (X ^ (ε ^ 2 / 2) / (ε * Real.log X)) ≤ (c - δ) * Work.BMF.pi0 P₂ :=
    mul_le_mul_of_nonneg_left hpi (le_of_lt hcδ)
  calc K * (M * Real.log (2 * P₁) + Real.log (X / (P₁ * P₂)) + 1) / Real.log (P₂ / 2)
      ≤ K * (Ab * Real.log X) / Real.log (P₂ / 2) := h1
    _ ≤ K * (Ab * Real.log X) / (ε ^ 2 / 4 * Real.log X) := h2
    _ = Cs := h3
    _ ≤ (c - δ) * (X ^ (ε ^ 2 / 2) / (ε * Real.log X)) := h5
    _ ≤ (c - δ) * Work.BMF.pi0 P₂ := h4

end Work.N8
