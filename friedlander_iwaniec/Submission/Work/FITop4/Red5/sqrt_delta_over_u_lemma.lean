import Mathlib

namespace Work.FITop4.Red5

/-
**Elementary `√`-comparison used in the thin-annulus crux.**

For `1 ≤ X₁ ≤ X₂`, `1 ≤ u` and `Δ ≥ 0`,
`√(Δu)/u ≤ 2(Δ(X₁u)^{-1/4} + (X₂u)^{1/4})`.

Proof.  Write `a = X₁u`, `b = X₂u`, so `1 ≤ a ≤ b`.  Since `√(Δu)/u = √Δ/√u`, and
`2(Δ a^{-1/4} + b^{1/4}) = (AΔ + B)/√u` for `A = 2 a^{-1/4}√u`, `B = 2 b^{1/4}√u`,
it suffices to prove `√Δ ≤ AΔ + B`.  This follows from `Δ ≤ (AΔ+B)²` (together with
`0 ≤ AΔ+B`), and
`(AΔ+B)² - Δ = (AΔ-B)² + (4AB-1)Δ ≥ 0`
since `4AB = 16 a^{-1/4}b^{1/4}u ≥ 16 ≥ 1`: indeed `a^{1/4} ≤ b^{1/4}` (as `a ≤ b`),
so `a^{-1/4}b^{1/4} = b^{1/4}/a^{1/4} ≥ 1`, and `u ≥ 1`.
-/
theorem sqrt_delta_over_u_lemma {X₁ X₂ u Δ : ℝ} (hX1 : 1 ≤ X₁) (hX2 : X₁ ≤ X₂) (hu : 1 ≤ u)
    (hΔ : 0 ≤ Δ) :
    Real.sqrt (Δ * u) / u
      ≤ 2 * (Δ * (X₁ * u) ^ (-(1 : ℝ) / 4) + (X₂ * u) ^ ((1 : ℝ) / 4)) := by
  have hu_pos : 0 < u := lt_of_lt_of_le one_pos hu
  have hX1_pos : 0 < X₁ := lt_of_lt_of_le one_pos hX1
  have hX2_pos : 0 < X₂ := lt_of_lt_of_le one_pos (le_trans hX1 hX2)
  have ha_pos : 0 < X₁ * u := mul_pos hX1_pos hu_pos
  have hb_pos : 0 < X₂ * u := mul_pos hX2_pos hu_pos
  have hab : X₁ * u ≤ X₂ * u := mul_le_mul_of_nonneg_right hX2 (le_of_lt hu_pos)
  have hsu_pos : 0 < Real.sqrt u := Real.sqrt_pos.mpr hu_pos
  have hsqrt2 : Real.sqrt u ^ 2 = u := Real.sq_sqrt (le_of_lt hu_pos)
  -- `(X₁u)^{-1/4} = ((X₁u)^{1/4})^{-1}`
  have hp1 : (X₁ * u) ^ (-(1 : ℝ) / 4) = ((X₁ * u) ^ ((1 : ℝ) / 4))⁻¹ := by
    have h : (-(1 : ℝ) / 4) = -((1 : ℝ) / 4) := by norm_num
    rw [h, Real.rpow_neg (le_of_lt ha_pos)]
  have hpq : (X₁ * u) ^ ((1 : ℝ) / 4) ≤ (X₂ * u) ^ ((1 : ℝ) / 4) :=
    Real.rpow_le_rpow (le_of_lt ha_pos) hab (by norm_num)
  have hp_pos : 0 < (X₁ * u) ^ ((1 : ℝ) / 4) := Real.rpow_pos_of_pos ha_pos _
  -- `1 ≤ a^{-1/4} b^{1/4}`
  have hr : 1 ≤ (X₁ * u) ^ (-(1 : ℝ) / 4) * (X₂ * u) ^ ((1 : ℝ) / 4) := by
    rw [hp1, inv_mul_eq_div, one_le_div hp_pos]
    exact hpq
  have h16 : 1 ≤ 16 * ((X₁ * u) ^ (-(1 : ℝ) / 4) * (X₂ * u) ^ ((1 : ℝ) / 4)) * u := by
    nlinarith [hr, hu]
  -- set `A = 2 a^{-1/4}√u`, `B = 2 b^{1/4}√u`
  set A := 2 * (X₁ * u) ^ (-(1 : ℝ) / 4) * Real.sqrt u with hA
  set B := 2 * (X₂ * u) ^ ((1 : ℝ) / 4) * Real.sqrt u with hB
  have hA_pos : 0 < A := by rw [hA]; positivity
  have hB_pos : 0 < B := by rw [hB]; positivity
  have hABeq : 4 * A * B
      = 16 * ((X₁ * u) ^ (-(1 : ℝ) / 4) * (X₂ * u) ^ ((1 : ℝ) / 4)) * u := by
    rw [hA, hB]
    ring_nf
    rw [hsqrt2]
    ring
  have hAB : 1 ≤ 4 * A * B := by rw [hABeq]; linarith [h16]
  have hkey : (A * Δ + B) ^ 2 - Δ = (A * Δ - B) ^ 2 + (4 * A * B - 1) * Δ := by ring
  have hΔAABB : Δ ≤ (A * Δ + B) ^ 2 := by
    have h1 : 0 ≤ (A * Δ - B) ^ 2 := sq_nonneg _
    have h2 : 0 ≤ (4 * A * B - 1) * Δ := mul_nonneg (by linarith) hΔ
    linarith [hkey, h1, h2]
  have hmain : Real.sqrt Δ ≤ A * Δ + B := by
    rw [Real.sqrt_le_iff]
    exact ⟨by nlinarith [hA_pos, hB_pos, hΔ], hΔAABB⟩
  -- `√(Δu)/u = √Δ/√u`
  have hL : Real.sqrt (Δ * u) / u = Real.sqrt Δ / Real.sqrt u := by
    rw [Real.sqrt_mul hΔ, div_eq_div_iff (ne_of_gt hu_pos) (ne_of_gt hsu_pos)]
    ring_nf
    rw [hsqrt2]
  -- `2(Δ a^{-1/4} + b^{1/4}) = (AΔ+B)/√u`
  have hrhs : 2 * (Δ * (X₁ * u) ^ (-(1 : ℝ) / 4) + (X₂ * u) ^ ((1 : ℝ) / 4))
      = (A * Δ + B) / Real.sqrt u := by
    rw [hA, hB, eq_div_iff (ne_of_gt hsu_pos)]
    ring
  rw [hL, hrhs]
  exact div_le_div_of_nonneg_right hmain (le_of_lt hsu_pos)

end Work.FITop4.Red5
