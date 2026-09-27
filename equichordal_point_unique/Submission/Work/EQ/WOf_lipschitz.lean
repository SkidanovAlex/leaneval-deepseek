import Mathlib
import Submission.Work.EQ.GermSetup
import Submission.Work.EQ.SqrtNearOne

/-!
# Lipschitz continuity of `WOf`

`WOf ρ u = (β)²/(1+S)` with `β = betaOf ρ u = -1 + u²·ρu` and
`S = SOf ρ u = sqHalf (u²β²)`.  Since `S² = 1 + u²β²` we have the exact identity
`u² · WOf ρ u = S - 1`, hence `WOf ρ₁ u - WOf ρ₂ u = (S₁ - S₂)/u²`, and
`S₁ - S₂` is controlled by the square-root Lipschitz estimate
`‖sqHalf z - sqHalf w‖ ≤ ‖z - w‖` applied to `z_i = u²β_i²`.

The elementary estimates (all with `R = ‖u‖`, `R ≤ eqLam a * germR a`):
* `‖β_i‖ ≤ 1 + R² ≤ 2`, so `‖β_1 + β_2‖ ≤ 4`;
* `β_1 - β_2 = u²(ρ₁ - ρ₂)`, so `‖β_1 - β_2‖ ≤ R² M`;
* `z_1 - z_2 = u²(β_1 - β_2)(β_1 + β_2)`, so `‖z_1 - z_2‖ ≤ R⁴ M · 4`;
* `‖W_1 - W_2‖ ≤ ‖z_1 - z_2‖/R² ≤ 4 R² M ≤ 4 λ² r² M ≤ 5 λ² r² M`.
-/

namespace Work.EQ

open Complex Metric Filter

noncomputable section

lemma betaOf_zero (ρ : ℂ → ℂ) : betaOf ρ 0 = -1 := by
  simp only [betaOf, zero_pow (by norm_num : (2 : ℕ) ≠ 0), zero_mul, add_zero]

lemma SOf_zero (ρ : ℂ → ℂ) : SOf ρ 0 = 1 := by
  simp only [SOf, betaOf, zero_pow (by norm_num : (2 : ℕ) ≠ 0), zero_mul, add_zero]
  exact Complex.one_cpow _

lemma WOf_zero (ρ : ℂ → ℂ) : WOf ρ 0 = 1 / 2 := by
  rw [WOf, betaOf_zero, SOf_zero]
  norm_num

lemma SOf_eq_sqHalf (ρ : ℂ → ℂ) (u : ℂ) :
    SOf ρ u = sqHalf (u ^ 2 * (betaOf ρ u) ^ 2) := rfl

lemma SOf_sq' (ρ : ℂ → ℂ) (u : ℂ) : SOf ρ u ^ 2 = 1 + u ^ 2 * (betaOf ρ u) ^ 2 := by
  rw [SOf_eq_sqHalf]
  exact sqHalf_sq _

/-- The exact identity `u² · WOf ρ u = S - 1`. -/
lemma WOf_mul_sq {ρ : ℂ → ℂ} {u : ℂ} (hz : ‖u ^ 2 * (betaOf ρ u) ^ 2‖ < 1) :
    WOf ρ u * u ^ 2 = SOf ρ u - 1 := by
  have h1S : (1 : ℂ) + SOf ρ u ≠ 0 := by
    rw [SOf_eq_sqHalf]
    have := sqHalf_add_one_ne_zero hz
    simpa only [add_comm] using this
  have hfac : (betaOf ρ u) ^ 2 * u ^ 2 = (SOf ρ u - 1) * (1 + SOf ρ u) := by
    rw [show (SOf ρ u - 1) * (1 + SOf ρ u) = SOf ρ u ^ 2 - 1 by ring]
    rw [SOf_sq' ρ u]
    ring
  rw [WOf, div_mul_eq_mul_div, div_eq_iff h1S]
  exact hfac

/-- `WOf ρ u = (S - 1)/u²` for `u ≠ 0`. -/
lemma WOf_eq_div' {ρ : ℂ → ℂ} {u : ℂ} (hu : u ≠ 0)
    (hz : ‖u ^ 2 * (betaOf ρ u) ^ 2‖ < 1) :
    WOf ρ u = (SOf ρ u - 1) / u ^ 2 := by
  rw [eq_div_iff (pow_ne_zero 2 hu)]
  exact WOf_mul_sq hz

theorem WOf_lipschitz {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {ρ₁ ρ₂ : ℂ → ℂ}
    (h₁ : ∀ z, ‖z‖ ≤ germR a → ‖ρ₁ z‖ ≤ 1) (h₂ : ∀ z, ‖z‖ ≤ germR a → ‖ρ₂ z‖ ≤ 1)
    {M : ℝ} (hM : ∀ z, ‖z‖ ≤ germR a → ‖ρ₁ z - ρ₂ z‖ ≤ M)
    {u : ℂ} (hu : ‖u‖ ≤ eqLam a * germR a) :
    ‖WOf ρ₁ u - WOf ρ₂ u‖ ≤ 5 * ((eqLam a) ^ 2 * (germR a) ^ 2) * M := by
  have hLp : 0 < eqLam a := eqLam_pos ha0 ha1
  have hrp : 0 < germR a := germR_pos ha0 ha1
  have hrnn : 0 ≤ germR a := le_of_lt hrp
  have hLr_nn : 0 ≤ eqLam a * germR a := mul_nonneg (le_of_lt hLp) hrnn
  have hMnn : 0 ≤ M := le_trans (norm_nonneg _) (hM 0 (by simpa using hrnn))
  have hu_le_r : ‖u‖ ≤ germR a := le_trans hu (lam_mul_germR_le_germR ha0 ha1)
  have hY : 0 ≤ (eqLam a) ^ 2 * (germR a) ^ 2 :=
    mul_nonneg (sq_nonneg _) (sq_nonneg _)
  rcases eq_or_ne u 0 with rfl | hune
  · -- degenerate case `u = 0`: both sides are `1/2`, difference `0`
    rw [WOf_zero, WOf_zero, sub_self, norm_zero]
    exact mul_nonneg (mul_nonneg (by norm_num) hY) hMnn
  · -- main case
    have hRpos : 0 < ‖u‖ := norm_pos_iff.mpr hune
    -- `R² = ‖u‖² ≤ (λ r)²`
    have hR2le : ‖u‖ ^ 2 ≤ (eqLam a) ^ 2 * (germR a) ^ 2 := by
      have h1 : ‖u‖ ^ 2 ≤ (eqLam a * germR a) ^ 2 := by
        nlinarith [hu, hLr_nn, norm_nonneg u]
      rwa [mul_pow] at h1
    have hR2le256 : ‖u‖ ^ 2 ≤ 1 / 256 :=
      le_trans hR2le (lam_sq_mul_germR_sq_le ha0 ha1)
    have hR2le1 : ‖u‖ ^ 2 ≤ 1 := by linarith
    have hR2nn : 0 ≤ ‖u‖ ^ 2 := sq_nonneg _
    have hR2pos : 0 < ‖u‖ ^ 2 := pow_pos hRpos 2
    -- bounds on `betaOf`
    have hb1 : ‖betaOf ρ₁ u‖ ≤ 1 + ‖u‖ ^ 2 := by
      rw [betaOf]
      calc ‖-1 + u ^ 2 * ρ₁ u‖
          ≤ ‖(-1 : ℂ)‖ + ‖u ^ 2 * ρ₁ u‖ := norm_add_le _ _
        _ = 1 + ‖u‖ ^ 2 * ‖ρ₁ u‖ := by rw [norm_neg, norm_one, norm_mul, norm_pow]
        _ ≤ 1 + ‖u‖ ^ 2 * 1 := by
              have h := mul_le_mul_of_nonneg_left (h₁ u hu_le_r) hR2nn
              linarith
        _ = 1 + ‖u‖ ^ 2 := by ring
    have hb2 : ‖betaOf ρ₂ u‖ ≤ 1 + ‖u‖ ^ 2 := by
      rw [betaOf]
      calc ‖-1 + u ^ 2 * ρ₂ u‖
          ≤ ‖(-1 : ℂ)‖ + ‖u ^ 2 * ρ₂ u‖ := norm_add_le _ _
        _ = 1 + ‖u‖ ^ 2 * ‖ρ₂ u‖ := by rw [norm_neg, norm_one, norm_mul, norm_pow]
        _ ≤ 1 + ‖u‖ ^ 2 * 1 := by
              have h := mul_le_mul_of_nonneg_left (h₂ u hu_le_r) hR2nn
              linarith
        _ = 1 + ‖u‖ ^ 2 := by ring
    have hb12 : ‖betaOf ρ₁ u + betaOf ρ₂ u‖ ≤ 4 := by
      calc ‖betaOf ρ₁ u + betaOf ρ₂ u‖
          ≤ ‖betaOf ρ₁ u‖ + ‖betaOf ρ₂ u‖ := norm_add_le _ _
        _ ≤ (1 + ‖u‖ ^ 2) + (1 + ‖u‖ ^ 2) := add_le_add hb1 hb2
        _ ≤ 4 := by linarith
    have hbd : ‖betaOf ρ₁ u - betaOf ρ₂ u‖ ≤ ‖u‖ ^ 2 * M := by
      have heq : betaOf ρ₁ u - betaOf ρ₂ u = u ^ 2 * (ρ₁ u - ρ₂ u) := by
        simp only [betaOf]; ring
      rw [heq, norm_mul, norm_pow]
      exact mul_le_mul_of_nonneg_left (hM u hu_le_r) hR2nn
    -- the square-root arguments stay in the disc of radius `1/2`
    have hz1 : ‖u ^ 2 * (betaOf ρ₁ u) ^ 2‖ ≤ 1 / 2 := by
      have hβ2 : ‖betaOf ρ₁ u‖ ^ 2 ≤ (1 + ‖u‖ ^ 2) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) hb1 2
      have hmul : ‖u‖ ^ 2 * ‖betaOf ρ₁ u‖ ^ 2 ≤ ‖u‖ ^ 2 * (1 + ‖u‖ ^ 2) ^ 2 :=
        mul_le_mul_of_nonneg_left hβ2 hR2nn
      have hfin : ‖u‖ ^ 2 * (1 + ‖u‖ ^ 2) ^ 2 ≤ 1 / 2 := by
        have hb : (1 + ‖u‖ ^ 2) ^ 2 ≤ 4 := by nlinarith [hR2le1, hR2nn]
        nlinarith [hR2le256, hR2nn, hb]
      calc ‖u ^ 2 * (betaOf ρ₁ u) ^ 2‖
          = ‖u‖ ^ 2 * ‖betaOf ρ₁ u‖ ^ 2 := by rw [norm_mul, norm_pow, norm_pow]
        _ ≤ ‖u‖ ^ 2 * (1 + ‖u‖ ^ 2) ^ 2 := hmul
        _ ≤ 1 / 2 := hfin
    have hz2 : ‖u ^ 2 * (betaOf ρ₂ u) ^ 2‖ ≤ 1 / 2 := by
      have hβ2 : ‖betaOf ρ₂ u‖ ^ 2 ≤ (1 + ‖u‖ ^ 2) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) hb2 2
      have hmul : ‖u‖ ^ 2 * ‖betaOf ρ₂ u‖ ^ 2 ≤ ‖u‖ ^ 2 * (1 + ‖u‖ ^ 2) ^ 2 :=
        mul_le_mul_of_nonneg_left hβ2 hR2nn
      have hfin : ‖u‖ ^ 2 * (1 + ‖u‖ ^ 2) ^ 2 ≤ 1 / 2 := by
        have hb : (1 + ‖u‖ ^ 2) ^ 2 ≤ 4 := by nlinarith [hR2le1, hR2nn]
        nlinarith [hR2le256, hR2nn, hb]
      calc ‖u ^ 2 * (betaOf ρ₂ u) ^ 2‖
          = ‖u‖ ^ 2 * ‖betaOf ρ₂ u‖ ^ 2 := by rw [norm_mul, norm_pow, norm_pow]
        _ ≤ ‖u‖ ^ 2 * (1 + ‖u‖ ^ 2) ^ 2 := hmul
        _ ≤ 1 / 2 := hfin
    -- difference of the square-root arguments
    have hZ : ‖u ^ 2 * (betaOf ρ₁ u) ^ 2 - u ^ 2 * (betaOf ρ₂ u) ^ 2‖
        ≤ (‖u‖ ^ 2 * (‖u‖ ^ 2 * M)) * 4 := by
      have heq : u ^ 2 * (betaOf ρ₁ u) ^ 2 - u ^ 2 * (betaOf ρ₂ u) ^ 2
          = (u ^ 2 * (betaOf ρ₁ u - betaOf ρ₂ u)) * (betaOf ρ₁ u + betaOf ρ₂ u) := by
        ring
      rw [heq, norm_mul, norm_mul, norm_pow]
      have hR2M : 0 ≤ ‖u‖ ^ 2 * (‖u‖ ^ 2 * M) :=
        mul_nonneg hR2nn (mul_nonneg hR2nn hMnn)
      exact mul_le_mul (mul_le_mul_of_nonneg_left hbd hR2nn) hb12 (norm_nonneg _) hR2M
    -- difference of the square roots
    have hSdiff : ‖SOf ρ₁ u - SOf ρ₂ u‖ ≤ (‖u‖ ^ 2 * (‖u‖ ^ 2 * M)) * 4 := by
      have h := norm_sqHalf_sub_sqHalf_le hz1 hz2
      rw [SOf_eq_sqHalf]
      exact le_trans h hZ
    -- difference of `WOf`
    have hW : WOf ρ₁ u - WOf ρ₂ u = (SOf ρ₁ u - SOf ρ₂ u) / u ^ 2 := by
      rw [WOf_eq_div' hune (lt_of_le_of_lt hz1 (by norm_num)),
          WOf_eq_div' hune (lt_of_le_of_lt hz2 (by norm_num))]
      ring
    have hfinal : ‖SOf ρ₁ u - SOf ρ₂ u‖ / ‖u‖ ^ 2
        ≤ 5 * ((eqLam a) ^ 2 * (germR a) ^ 2) * M := by
      have h1 : ‖SOf ρ₁ u - SOf ρ₂ u‖ / ‖u‖ ^ 2
          ≤ ((‖u‖ ^ 2 * (‖u‖ ^ 2 * M)) * 4) / ‖u‖ ^ 2 :=
        div_le_div_of_nonneg_right hSdiff (le_of_lt hR2pos)
      have h2 : ((‖u‖ ^ 2 * (‖u‖ ^ 2 * M)) * 4) / ‖u‖ ^ 2 = 4 * ‖u‖ ^ 2 * M := by
        rw [div_eq_iff (ne_of_gt hR2pos)]
        ring
      have h3 : 4 * ‖u‖ ^ 2 * M ≤ 5 * ((eqLam a) ^ 2 * (germR a) ^ 2) * M := by
        nlinarith [hR2le, hY, hMnn, hR2nn]
      linarith [h1, le_of_eq h2, h3]
    rw [hW, norm_div, norm_pow]
    exact hfinal

end

end Work.EQ
