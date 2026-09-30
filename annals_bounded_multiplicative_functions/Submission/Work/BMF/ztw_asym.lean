import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Asymptotic helpers for the `6/7`-shaped twisted Perron parameters

Routine growth comparisons between powers of `L`, `log L` and exponentials of
`L ^ c`, collected once so that the numeric parameter package
`Work.BMF.ztw_param` can be assembled from them.
-/

namespace Work.BMF

open Filter
open scoped Real Topology

noncomputable section

/-- `log` grows more slowly than any positive power: for any `c : ℝ` and `0 < b`,
eventually `c * log L ≤ L ^ b`. -/
lemma ztw_log_le_rpow (c b : ℝ) (hb : 0 < b) :
    ∀ᶠ L : ℝ in atTop, c * Real.log L ≤ L ^ b := by
  rcases lt_or_ge c 0 with hc | hc
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with L hL
    exact le_trans (mul_nonpos_of_nonpos_of_nonneg hc.le (Real.log_nonneg hL))
      (Real.rpow_nonneg (by linarith) b)
  · have h := (isLittleO_log_rpow_rpow_atTop (1 : ℝ) hb).const_mul_left c
    filter_upwards [h.eventuallyLE, eventually_ge_atTop (1 : ℝ)] with L hL hL1
    simp only [Real.rpow_one] at hL
    rw [Real.norm_of_nonneg (mul_nonneg hc (Real.log_nonneg hL1)),
        Real.norm_of_nonneg (Real.rpow_nonneg (by linarith) b)] at hL
    exact hL

/-- A polynomial is eventually dominated by `exp (b * L ^ c)` when `b, c > 0`. -/
lemma ztw_rpow_le_exp (K a b c : ℝ) (hK : 0 ≤ K) (hb : 0 < b) (hc : 0 < c) :
    ∀ᶠ L : ℝ in atTop, K * L ^ a ≤ Real.exp (b * L ^ c) := by
  rcases eq_or_lt_of_le hK with hK0 | hKpos
  · filter_upwards with L
    rw [← hK0, zero_mul]
    exact (Real.exp_pos _).le
  · have hb2 : 0 < b / 2 := by positivity
    have ha : ∀ᶠ L : ℝ in atTop, a * Real.log L ≤ b / 2 * L ^ c := by
      have h := ztw_log_le_rpow (2 * a / b) c hc
      filter_upwards [h] with L hL
      have h2 := mul_le_mul_of_nonneg_left hL hb2.le
      have he : b / 2 * (2 * a / b * Real.log L) = a * Real.log L := by
        field_simp
      linarith [he ▸ h2]
    have hlogK : ∀ᶠ L : ℝ in atTop, Real.log K ≤ b / 2 * L ^ c := by
      filter_upwards [(tendsto_rpow_atTop hc).eventually_ge_atTop (2 * Real.log K / b)] with L hL
      have h2 := mul_le_mul_of_nonneg_left hL hb2.le
      have he : b / 2 * (2 * Real.log K / b) = Real.log K := by
        field_simp
      linarith [he ▸ h2]
    filter_upwards [ha, hlogK, eventually_gt_atTop (0 : ℝ)] with L haL hkL hLpos
    have hKexp : K = Real.exp (Real.log K) := (Real.exp_log hKpos).symm
    have hmain : K * L ^ a = Real.exp (Real.log K + Real.log L * a) := by
      calc K * L ^ a = Real.exp (Real.log K) * L ^ a := by
            conv_lhs => rw [hKexp]
        _ = Real.exp (Real.log K) * Real.exp (Real.log L * a) := by
            rw [Real.rpow_def_of_pos hLpos a]
        _ = Real.exp (Real.log K + Real.log L * a) := by rw [Real.exp_add]
    rw [hmain, Real.exp_le_exp]
    linarith [haL, hkL]

/-- A polynomial times a decaying exponential is eventually below any positive `ε`. -/
lemma ztw_rpow_mul_exp_neg_le (K a b c ε : ℝ) (hK : 0 ≤ K) (hb : 0 < b) (hc : 0 < c)
    (hε : 0 < ε) :
    ∀ᶠ L : ℝ in atTop, K * L ^ a * Real.exp (-(b * L ^ c)) ≤ ε := by
  have hb2 : 0 < b / 2 := by positivity
  have h1 : ∀ᶠ L : ℝ in atTop, K * L ^ a ≤ Real.exp (b / 2 * L ^ c) :=
    ztw_rpow_le_exp K a (b / 2) c hK hb2 hc
  have h2 : ∀ᶠ L : ℝ in atTop, Real.exp (-(b / 2 * L ^ c)) ≤ ε := by
    filter_upwards [(tendsto_rpow_atTop hc).eventually_ge_atTop (-Real.log ε / (b / 2))]
      with L hL
    rw [← Real.exp_log hε, Real.exp_le_exp]
    have h2' := mul_le_mul_of_nonneg_left hL hb2.le
    have he : b / 2 * (-Real.log ε / (b / 2)) = -Real.log ε := by
      field_simp
    linarith [he ▸ h2']
  filter_upwards [h1, h2] with L hL1 hL2
  calc K * L ^ a * Real.exp (-(b * L ^ c))
      ≤ Real.exp (b / 2 * L ^ c) * Real.exp (-(b * L ^ c)) :=
        mul_le_mul_of_nonneg_right hL1 (Real.exp_pos _).le
    _ = Real.exp (b / 2 * L ^ c + -(b * L ^ c)) := by rw [Real.exp_add]
    _ = Real.exp (-(b / 2 * L ^ c)) := by
        congr 1
        ring
    _ ≤ ε := hL2

/-- A polynomial times `exp (-(b₁ L^{c₁} - b₂ L^{c₂}))` with `0 < c₂ < c₁`, `b₁ > 0`,
`b₂ ≥ 0` is eventually below any positive `ε`. -/
lemma ztw_rpow_mul_exp_sub_le (K a b₁ b₂ c₁ c₂ ε : ℝ) (hK : 0 ≤ K) (hb₁ : 0 < b₁)
    (_hb₂ : 0 ≤ b₂) (hc₁ : 0 < c₁) (_hc₂ : 0 < c₂) (hcc : c₂ < c₁) (hε : 0 < ε) :
    ∀ᶠ L : ℝ in atTop, K * L ^ a * Real.exp (-(b₁ * L ^ c₁ - b₂ * L ^ c₂)) ≤ ε := by
  have hb1h : 0 < b₁ / 2 := by positivity
  have hb2le : ∀ᶠ L : ℝ in atTop, b₂ * L ^ c₂ ≤ b₁ / 2 * L ^ c₁ := by
    have hd : 0 < c₁ - c₂ := sub_pos.mpr hcc
    filter_upwards [eventually_gt_atTop (0 : ℝ),
      (tendsto_rpow_atTop hd).eventually_ge_atTop (2 * b₂ / b₁)] with L hLpos hL
    have hsplit : L ^ c₁ = L ^ c₂ * L ^ (c₁ - c₂) := by
      rw [← Real.rpow_add hLpos]
      ring_nf
    have hLcpos : 0 < L ^ c₂ := Real.rpow_pos_of_pos hLpos c₂
    have hstep : b₂ ≤ b₁ / 2 * L ^ (c₁ - c₂) := by
      have h2' := mul_le_mul_of_nonneg_left hL hb1h.le
      have he : b₁ / 2 * (2 * b₂ / b₁) = b₂ := by
        field_simp
      linarith [he ▸ h2']
    calc b₂ * L ^ c₂ ≤ (b₁ / 2 * L ^ (c₁ - c₂)) * L ^ c₂ :=
          mul_le_mul_of_nonneg_right hstep hLcpos.le
      _ = b₁ / 2 * L ^ c₁ := by rw [hsplit]; ring
  have hmain : ∀ᶠ L : ℝ in atTop, K * L ^ a * Real.exp (-(b₁ / 2 * L ^ c₁)) ≤ ε :=
    ztw_rpow_mul_exp_neg_le K a (b₁ / 2) c₁ ε hK hb1h hc₁ hε
  filter_upwards [hb2le, hmain, eventually_ge_atTop (0 : ℝ)] with L hle hm hL0
  calc K * L ^ a * Real.exp (-(b₁ * L ^ c₁ - b₂ * L ^ c₂))
      ≤ K * L ^ a * Real.exp (-(b₁ / 2 * L ^ c₁)) := by
        apply mul_le_mul_of_nonneg_left _ (mul_nonneg hK (Real.rpow_nonneg hL0 a))
        apply Real.exp_le_exp.mpr
        linarith
    _ ≤ ε := hm

end

end Work.BMF
