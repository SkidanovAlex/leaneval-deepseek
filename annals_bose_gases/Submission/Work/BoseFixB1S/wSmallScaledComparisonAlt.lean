import ChallengeDeps
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseFixB1S.abs_wSmallScaled_div_convScale_le
import Submission.Work.MGroupInput.newtonianSharp
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The sharp pointwise comparison of the two-factor renormalised kernel with `g₀`

Self-contained proof of the comparison used by `Work.BoseFixB1S.slidingNewtonMassSharpB1`:
for the sliding kernel

    𝒲 = wSmallScaled M (ℓ·d) (g₀) / convScale ℓ ,

on the a.e. set where `g₀ ≥ 0`,

    0 ≤ 𝒲 ,      𝒲 ≤ (1 + (2C₂/smallConvLower M)·(R/(ℓd))² + 2C₁·(R/ℓ)²)·g₀ ,

where `C₂` bounds the global quadratic deviation of `(χ_M⋆χ_M)` from `1` and `C₁` the same for
`(χ⋆χ)`.  On the support of `g₀` (`‖x‖ < R`) the two denominators
`a := (χ_M⋆χ_M)(x/(ℓd))` and `b := (χ⋆χ)(x/ℓ)` satisfy

    smallConvLower M ≤ a ≤ 1        (`|x/(ℓd)| ≤ 1/16`, `conv3Small_coord_lower`/`conv3Small_abs_le_one`),
    1/2 ≤ b ≤ 1                     (`R ≤ ℓ·chiR0`, `convScale_ge_half_ball`; `conv3chi_le_one`),

and `1 - a ≤ C₂(R/(ℓd))²`, `1 - b ≤ C₁(R/ℓ)²`, so that
`1/(ab) - 1 = (1-a)/(ab) + (1-b)/b ≤ (2/smallConvLower M)(1-a) + 2(1-b)`.
Off the support both sides vanish.

This module is written so that it does not depend on the separately delegated
`Work.BoseFixB1S.wSmallScaled_sharp_comparison` / its helpers.
-/

namespace Work.BoseFixB1S

open MeasureTheory Metric
open scoped Real BigOperators ENNReal

local notation "E3" => EuclideanSpace ℝ (Fin 3)

set_option maxHeartbeats 1000000
set_option linter.unusedVariables false

/-- **Deviation of the `ℓ`-factor**: `1 - (χ⋆χ)(x/ℓ) ≤ C₁(R/ℓ)²` on `‖x‖ ≤ R`, from a global
quadratic deviation bound for `(χ⋆χ)`. -/
lemma convScale_dev_le {C₁ R ℓ : ℝ} (hC₁0 : 0 ≤ C₁)
    (hC₁ : ∀ t : E3, |Submission.BoseGases.conv3 Submission.BoseGases.chi
      Submission.BoseGases.chi t - 1| ≤ C₁ * ‖t‖ ^ 2)
    (hℓ : 0 < ℓ) {x : E3} (hx : ‖x‖ ≤ R) :
    1 - Submission.BoseGases.convScale ℓ x ≤ C₁ * (R / ℓ) ^ 2 := by
  have hdev := hC₁ ((ℓ⁻¹) • x)
  have hlow : (1 : ℝ) - Submission.BoseGases.conv3 Submission.BoseGases.chi
      Submission.BoseGases.chi ((ℓ⁻¹) • x) ≤ C₁ * ‖(ℓ⁻¹) • x‖ ^ 2 := by
    have h := (abs_le.mp hdev).1
    linarith
  have hnorm : ‖(ℓ⁻¹) • x‖ ≤ R / ℓ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hℓ)]
    calc ℓ⁻¹ * ‖x‖ ≤ ℓ⁻¹ * R := mul_le_mul_of_nonneg_left hx (inv_pos.mpr hℓ).le
      _ = R / ℓ := by ring
  calc 1 - Submission.BoseGases.convScale ℓ x
      = 1 - Submission.BoseGases.conv3 Submission.BoseGases.chi Submission.BoseGases.chi
          ((ℓ⁻¹) • x) := rfl
    _ ≤ C₁ * ‖(ℓ⁻¹) • x‖ ^ 2 := hlow
    _ ≤ C₁ * (R / ℓ) ^ 2 :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hnorm 2) hC₁0

/-- **Deviation of the `ℓd`-factor**: `1 - (χ_M⋆χ_M)(x/(ℓd)) ≤ C₂(R/(ℓd))²` on `‖x‖ ≤ R`, from a
global quadratic deviation bound for `(χ_M⋆χ_M)`. -/
lemma convScaleSmall_dev_le {M : ℕ} {C₂ R ℓ d : ℝ} (hC₂0 : 0 ≤ C₂)
    (hC₂ : ∀ t : E3, |Submission.BoseGases.conv3Small M t - 1| ≤ C₂ * ‖t‖ ^ 2)
    (hℓ : 0 < ℓ) (hd : 0 < d) {x : E3} (hx : ‖x‖ ≤ R) :
    1 - Submission.BoseGases.convScaleSmall M (ℓ * d) x ≤ C₂ * (R / (ℓ * d)) ^ 2 := by
  have hld : 0 < ℓ * d := mul_pos hℓ hd
  have hdev := hC₂ (((ℓ * d)⁻¹) • x)
  have hlow : (1 : ℝ) - Submission.BoseGases.conv3Small M (((ℓ * d)⁻¹) • x)
      ≤ C₂ * ‖((ℓ * d)⁻¹) • x‖ ^ 2 := by
    have h := (abs_le.mp hdev).1
    linarith
  have hnorm : ‖((ℓ * d)⁻¹) • x‖ ≤ R / (ℓ * d) := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hld)]
    calc (ℓ * d)⁻¹ * ‖x‖ ≤ (ℓ * d)⁻¹ * R := mul_le_mul_of_nonneg_left hx (inv_pos.mpr hld).le
      _ = R / (ℓ * d) := by ring
  calc 1 - Submission.BoseGases.convScaleSmall M (ℓ * d) x
      = 1 - Submission.BoseGases.conv3Small M (((ℓ * d)⁻¹) • x) := rfl
    _ ≤ C₂ * ‖((ℓ * d)⁻¹) • x‖ ^ 2 := hlow
    _ ≤ C₂ * (R / (ℓ * d)) ^ 2 :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hnorm 2) hC₂0

/-- **Reciprocal arithmetic of the comparison**: with `S ≤ a ≤ 1`, `1/2 ≤ b ≤ 1`,
`1 - a ≤ c₂`, `1 - b ≤ c₁` (all positive), `1/(ab) ≤ 1 + 2c₂/S + 2c₁`. -/
lemma sharp_comparison_arith {S a b c₁ c₂ : ℝ} (hS : 0 < S) (ha0 : 0 < a) (hb0 : 0 < b)
    (ha₁ : a ≤ 1) (hb₁ : b ≤ 1) (haS : S ≤ a) (hbhalf : 1 / 2 ≤ b)
    (hadev : 1 - a ≤ c₂) (hbdev : 1 - b ≤ c₁) :
    (a * b)⁻¹ ≤ 1 + 2 * c₂ / S + 2 * c₁ := by
  have ha0' : 0 ≤ 1 - a := by linarith
  have hb0' : 0 ≤ 1 - b := by linarith
  have hab : 0 < a * b := mul_pos ha0 hb0
  have hinvAB : (a * b)⁻¹ ≤ 2 / S := by
    rw [le_div_iff₀ hS, inv_mul_eq_div, div_le_iff₀ hab]
    nlinarith [haS, hbhalf, ha0, hb0]
  have hinvB : b⁻¹ ≤ 2 := by
    rw [inv_le_comm₀ hb0 (by norm_num)]
    linarith
  have hsplit : (a * b)⁻¹ = 1 + (1 - a) * (a * b)⁻¹ + (1 - b) * b⁻¹ := by
    field_simp
    ring
  have h1 : (1 - a) * (a * b)⁻¹ ≤ (1 - a) * (2 / S) :=
    mul_le_mul_of_nonneg_left hinvAB ha0'
  have h2 : (1 - a) * (2 / S) ≤ c₂ * (2 / S) :=
    mul_le_mul_of_nonneg_right hadev (by positivity)
  have h2' : c₂ * (2 / S) = 2 * c₂ / S := by ring
  have h3 : (1 - b) * b⁻¹ ≤ (1 - b) * 2 := mul_le_mul_of_nonneg_left hinvB hb0'
  have h4 : (1 - b) * 2 ≤ c₁ * 2 := mul_le_mul_of_nonneg_right hbdev (by norm_num)
  have hA : (1 - a) * (a * b)⁻¹ ≤ 2 * c₂ / S := by linarith
  have hB : (1 - b) * b⁻¹ ≤ 2 * c₁ := by linarith
  rw [hsplit]
  linarith

/-- **Sharp pointwise (a.e.) comparison of the two-factor renormalised kernel with `g₀`.**

For the sliding kernel `𝒲 = wSmallScaled M (ℓ·d) (g₀) / convScale ℓ`, everywhere except on the
negligible set where `g₀ < 0`, one has `0 ≤ 𝒲` and
`𝒲 ≤ (1 + 2C₂/smallConvLower M·(R/(ℓ·d))² + 2C₁·(R/ℓ)²)·g₀`, where `C₁` (resp. `C₂`) is a global
quadratic-deviation constant for `(χ⋆χ)` (resp. `(χ_M⋆χ_M)`). -/
theorem wSmallScaled_sharp_comparison_alt {v : E3 → ℝ} {R : ℝ}
    (hv_supp : tsupport v ⊆ Metric.ball (0 : E3) R) (hR0 : 0 < R)
    (hv : 0 ≤ v) (hvrad : _root_.BoseGases.IsRadial v) (h : Work.UBB.ScatSol v)
    {M : ℕ} (hM : 1 ≤ M) {C₁ C₂ : ℝ} (hC₁0 : 0 ≤ C₁) (hC₂0 : 0 ≤ C₂)
    (hC₁ : ∀ t : E3, |Submission.BoseGases.conv3 Submission.BoseGases.chi
      Submission.BoseGases.chi t - 1| ≤ C₁ * ‖t‖ ^ 2)
    (hC₂ : ∀ t : E3, |Submission.BoseGases.conv3Small M t - 1| ≤ C₂ * ‖t‖ ^ 2)
    {ℓ d : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d)
    (hR : R ≤ ℓ * d / 16) (hRχ : R ≤ ℓ * Submission.BoseGases.chiR0) :
    ∀ᵐ x : E3,
      0 ≤ Submission.BoseGases.wSmallScaled M (ℓ * d) (Submission.BoseGases.g0 v h) x
          / Submission.BoseGases.convScale ℓ x
      ∧ Submission.BoseGases.wSmallScaled M (ℓ * d) (Submission.BoseGases.g0 v h) x
          / Submission.BoseGases.convScale ℓ x
        ≤ (1 + 2 * C₂ / Work.SmallBoxSliding.smallConvLower M * (R / (ℓ * d)) ^ 2
            + 2 * C₁ * (R / ℓ) ^ 2) * Submission.BoseGases.g0 v h x := by
  filter_upwards [Submission.BoseGases.g0_nonneg_ae hR0 hv hvrad hv_supp h] with x hg0x
  by_cases hx : ‖x‖ ≤ R
  · have hld : 0 < ℓ * d := mul_pos hℓ hd
    have hsS : 0 < Work.SmallBoxSliding.smallConvLower M :=
      Work.SmallBoxSliding.smallConvLower_pos M
    -- the `ℓd`-denominator
    have hu1 : ‖((ℓ * d)⁻¹) • x‖ ≤ 1 / 16 := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hld)]
      have h1 : (ℓ * d)⁻¹ * ‖x‖ ≤ (ℓ * d)⁻¹ * R := mul_le_mul_of_nonneg_left hx (inv_pos.mpr hld).le
      have h2 : (ℓ * d)⁻¹ * R ≤ (ℓ * d)⁻¹ * ((ℓ * d) / 16) :=
        mul_le_mul_of_nonneg_left hR (inv_pos.mpr hld).le
      have h3 : (ℓ * d)⁻¹ * ((ℓ * d) / 16) = 1 / 16 := by field_simp
      linarith
    have hcoord : ∀ j : Fin 3, |(((ℓ * d)⁻¹) • x).ofLp j| ≤ 1 / 16 :=
      fun j => le_trans (Submission.BoseGases.coord_abs_le_norm _ j) hu1
    have haS : Work.SmallBoxSliding.smallConvLower M
        ≤ Submission.BoseGases.convScaleSmall M (ℓ * d) x :=
      Work.SmallBoxSliding.conv3Small_coord_lower hM _ hcoord
    have ha0 : 0 < Submission.BoseGases.convScaleSmall M (ℓ * d) x := lt_of_lt_of_le hsS haS
    have ha1 : Submission.BoseGases.convScaleSmall M (ℓ * d) x ≤ 1 := by
      have h := Submission.BoseGases.conv3Small_abs_le_one hM (((ℓ * d)⁻¹) • x)
      rw [abs_le] at h
      exact h.2
    -- the `ℓ`-denominator
    have hbhalf : 1 / 2 ≤ Submission.BoseGases.convScale ℓ x :=
      Submission.BoseGases.convScale_ge_half_ball hℓ hR0.le hRχ hx
    have hb0 : 0 < Submission.BoseGases.convScale ℓ x := lt_of_lt_of_le (by norm_num) hbhalf
    have hb1 : Submission.BoseGases.convScale ℓ x ≤ 1 :=
      Submission.BoseGases.conv3chi_le_one ((ℓ⁻¹) • x)
    -- deviations
    have hadev : 1 - Submission.BoseGases.convScaleSmall M (ℓ * d) x ≤ C₂ * (R / (ℓ * d)) ^ 2 :=
      convScaleSmall_dev_le hC₂0 hC₂ hℓ hd hx
    have hbdev : 1 - Submission.BoseGases.convScale ℓ x ≤ C₁ * (R / ℓ) ^ 2 :=
      convScale_dev_le hC₁0 hC₁ hℓ hx
    have harith := sharp_comparison_arith hsS ha0 hb0 ha1 hb1 haS hbhalf hadev hbdev
    have hW : Submission.BoseGases.wSmallScaled M (ℓ * d) (Submission.BoseGases.g0 v h) x
          / Submission.BoseGases.convScale ℓ x
        = Submission.BoseGases.g0 v h x
          * (Submission.BoseGases.convScaleSmall M (ℓ * d) x
              * Submission.BoseGases.convScale ℓ x)⁻¹ := by
      rw [show Submission.BoseGases.wSmallScaled M (ℓ * d) (Submission.BoseGases.g0 v h) x
            = Submission.BoseGases.g0 v h x / Submission.BoseGases.convScaleSmall M (ℓ * d) x
            from rfl, div_div, div_eq_mul_inv]
    refine ⟨?_, ?_⟩
    · rw [hW]
      exact mul_nonneg hg0x (inv_nonneg.mpr (mul_pos ha0 hb0).le)
    · rw [hW]
      calc Submission.BoseGases.g0 v h x
            * (Submission.BoseGases.convScaleSmall M (ℓ * d) x
                * Submission.BoseGases.convScale ℓ x)⁻¹
          ≤ Submission.BoseGases.g0 v h x
              * (1 + 2 * (C₂ * (R / (ℓ * d)) ^ 2) / Work.SmallBoxSliding.smallConvLower M
                  + 2 * (C₁ * (R / ℓ) ^ 2)) :=
            mul_le_mul_of_nonneg_left harith hg0x
        _ = (1 + 2 * C₂ / Work.SmallBoxSliding.smallConvLower M * (R / (ℓ * d)) ^ 2
              + 2 * C₁ * (R / ℓ) ^ 2) * Submission.BoseGases.g0 v h x := by ring
  · have hxg : R < ‖x‖ := lt_of_not_ge hx
    have hz0 : Submission.BoseGases.g0 v h x = 0 :=
      Submission.BoseGases.g0_zero_of_norm_ge hv_supp (le_of_lt hxg) h
    have hW0 : Submission.BoseGases.wSmallScaled M (ℓ * d) (Submission.BoseGases.g0 v h) x
        / Submission.BoseGases.convScale ℓ x = 0 := by
      simp [Submission.BoseGases.wSmallScaled, hz0]
    refine ⟨by simp [hW0], by simp [hW0, hz0]⟩

end Work.BoseFixB1S
