import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.C.geoCrux.sharp

/-- Elementary half-angle bound: for `0 < ρ < π`,
`tan (ρ/2) * sin ρ = 2 sin²(ρ/2) ≤ 2`. -/
lemma tan_half_mul_sin_le {ρ : ℝ} (hρ0 : 0 < ρ) (hρπ : ρ < Real.pi) :
    Real.tan (ρ / 2) * Real.sin ρ ≤ 2 := by
  have hcos_pos : 0 < Real.cos (ρ / 2) := by
    apply Real.cos_pos_of_mem_Ioo
    constructor <;> linarith [Real.pi_pos]
  have hsin2 : Real.sin ρ = 2 * Real.sin (ρ / 2) * Real.cos (ρ / 2) := by
    have h := Real.sin_two_mul (ρ / 2)
    rwa [show 2 * (ρ / 2) = ρ from by ring] at h
  calc Real.tan (ρ / 2) * Real.sin ρ
      = (Real.sin (ρ / 2) / Real.cos (ρ / 2)) * Real.sin ρ := by
        rw [Real.tan_eq_sin_div_cos]
    _ = (Real.sin (ρ / 2) / Real.cos (ρ / 2)) * (2 * Real.sin (ρ / 2) * Real.cos (ρ / 2)) := by
        rw [hsin2]
    _ = 2 * Real.sin (ρ / 2) ^ 2 := by
        field_simp
    _ ≤ 2 := by
        nlinarith [Real.sin_sq_le_one (ρ / 2)]

theorem anchor_arith {c ε₁ ρ : ℝ} (hc : 0 < c) (hc1 : c ≤ 1 / 4)
    (hε₁ : 0 ≤ ε₁) (hnum2 : 4 * ε₁ * Real.pi < c)
    (hρ : Real.pi / 3 < ρ) (hρπ : ρ ≤ Real.pi - Real.arccos (1 - c)) :
    (1 + 7 * ε₁) * (Real.tan (ρ / 2) / Real.tan (Real.pi / 6)) ^ ε₁
      ≤ 1 + 25 * ε₁ / Real.sin ρ := by
  set R : ℝ := Real.tan (ρ / 2) / Real.tan (Real.pi / 6) with hR
  set s : ℝ := Real.sin ρ with hs
  -- Basic ranges.
  have hρ_lt_pi : ρ < Real.pi := by
    have : 0 < Real.arccos (1 - c) := Real.arccos_pos.mpr (by linarith)
    linarith
  have hρ_pos : 0 < ρ := by linarith [Real.pi_pos]
  have hs_pos : 0 < s := by
    rw [hs]; exact Real.sin_pos_of_pos_of_lt_pi hρ_pos hρ_lt_pi
  have hs_le : s ≤ 1 := by rw [hs]; exact Real.sin_le_one ρ
  -- `ε₁ < 1/16`, from `4 ε₁ π < c ≤ 1/4`.
  have hε₁_lt : ε₁ < 1 / 16 := by
    have h₁ : ε₁ * Real.pi < 1 / 16 := by nlinarith [hnum2, hc1]
    nlinarith [Real.pi_gt_three, hε₁, h₁]
  -- The ratio `R` equals `√3 · tan (ρ/2)`.
  have htan_half_pos : 0 < Real.tan (ρ / 2) :=
    Real.tan_pos_of_pos_of_lt_pi_div_two (by linarith) (by linarith)
  have hR_eq : R = Real.sqrt 3 * Real.tan (ρ / 2) := by
    rw [hR, Real.tan_pi_div_six]
    field_simp
  have hR_nonneg : 0 ≤ R := by
    rw [hR_eq]; exact mul_nonneg (Real.sqrt_nonneg 3) htan_half_pos.le
  -- Step 1: weighted geometric–arithmetic mean (chord bound for the `ε₁`-power).
  have hstep1 : R ^ ε₁ ≤ 1 + ε₁ * (R - 1) := by
    have h := Real.geom_mean_le_arith_mean2_weighted (w₁ := ε₁) (w₂ := 1 - ε₁)
      (p₁ := R) (p₂ := 1) hε₁ (by linarith) hR_nonneg (by norm_num) (by ring)
    rw [Real.one_rpow, mul_one] at h
    calc R ^ ε₁ ≤ ε₁ * R + (1 - ε₁) * 1 := h
      _ = 1 + ε₁ * (R - 1) := by ring
  -- Step 2: `R * s ≤ 4`.
  have hRs : R * s ≤ 4 := by
    rw [hR_eq, hs]
    have h := tan_half_mul_sin_le hρ_pos hρ_lt_pi
    have h3 : Real.sqrt 3 ≤ 2 := by
      nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num), Real.sqrt_nonneg 3]
    have h1 : Real.sqrt 3 * (Real.tan (ρ / 2) * Real.sin ρ) ≤ Real.sqrt 3 * 2 :=
      mul_le_mul_of_nonneg_left h (Real.sqrt_nonneg 3)
    nlinarith [h1, h3, Real.sqrt_nonneg 3]
  -- Step 3: `(R - 1) * (1 + 7ε₁) * s ≤ 6`.
  have hdiff : (R - 1) * (1 + 7 * ε₁) * s ≤ 6 := by
    have hX : 0 ≤ (1 + 7 * ε₁) * s := mul_nonneg (by linarith) hs_pos.le
    have h1 : (R - 1) * (1 + 7 * ε₁) * s ≤ R * (1 + 7 * ε₁) * s := by
      calc (R - 1) * (1 + 7 * ε₁) * s = (R - 1) * ((1 + 7 * ε₁) * s) := by ring
        _ ≤ R * ((1 + 7 * ε₁) * s) :=
            mul_le_mul_of_nonneg_right (by linarith : R - 1 ≤ R) hX
        _ = R * (1 + 7 * ε₁) * s := by ring
    have h2 : R * (1 + 7 * ε₁) * s ≤ 4 * (23 / 16) := by
      have hle : (1 + 7 * ε₁) ≤ 23 / 16 := by linarith
      calc R * (1 + 7 * ε₁) * s = (R * s) * (1 + 7 * ε₁) := by ring
        _ ≤ 4 * (23 / 16) := mul_le_mul hRs hle (by linarith) (by norm_num)
    linarith
  -- Step 4: `(R - 1) * (1 + 7ε₁) + 7 ≤ 25 / s`.
  have hbound : (R - 1) * (1 + 7 * ε₁) + 7 ≤ 25 / s := by
    have h6 : (R - 1) * (1 + 7 * ε₁) ≤ 6 / s := by
      rw [le_div_iff₀ hs_pos]; linarith
    have h7 : (7 : ℝ) ≤ 19 / s := by
      rw [le_div_iff₀ hs_pos]; nlinarith [hs_le]
    have heq : (6 : ℝ) / s + 19 / s = 25 / s := by ring
    linarith
  -- Assembly.
  calc (1 + 7 * ε₁) * R ^ ε₁
      ≤ (1 + 7 * ε₁) * (1 + ε₁ * (R - 1)) :=
        mul_le_mul_of_nonneg_left hstep1 (by linarith)
    _ = 1 + ε₁ * ((R - 1) * (1 + 7 * ε₁) + 7) := by ring
    _ ≤ 1 + ε₁ * (25 / s) :=
        add_le_add le_rfl (mul_le_mul_of_nonneg_left hbound hε₁)
    _ = 1 + 25 * ε₁ / s := by ring

end Work.Diff.C.geoCrux.sharp
