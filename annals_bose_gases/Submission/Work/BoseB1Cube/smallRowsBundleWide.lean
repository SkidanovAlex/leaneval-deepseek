import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseB1Cube.smallRowsBundle
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseB1Cube

set_option maxHeartbeats 1000000
set_option linter.unusedVariables false

/-!
# `Work.BoseB1Cube.smallRowsBundleWide`

The `Cn`-scaled version of the PROVED `Work.BoseB1Cube.smallRowsBundle`: the same seven rows of the
cube ledger, over the density window `4μ ≤ n/V ≤ 2·Cn·μ` (`Cn ≥ 4`) and the box-volume gate
`64·Cn ≤ μV` in place of `n/V ≤ 5μ` and `64 ≤ μV`.

The proof is a term-by-term comparison, exactly parallel to `smallRowsBundle`: each row is isolated
in its own small lemma so that the arithmetic tactics see a minimal context.  Every row bound is
stated against the *same* normalised monomial `μ²·M₁` that occurs in the target, which is what lets
the final `linarith` combine the seven rows.  The two master estimates are

* `Cn·μ/V ≤ μ²/64` (from `64·Cn ≤ μV`), which turns `2·Cn·μ/V` into `μ²/32`, and
* `μ/V ≤ μ²/64` (from `Cn ≥ 1` and `64·Cn ≤ μV`), which handles the chemical-potential row.

The row constants are `1/32, 1/128, 1/128, 9/256, 1/32, 1/32, 1/20`, whose sum is
`37/256 + 1/20 = 996/5120 < 1/2`.
-/

/-! ## §1. The two master estimates -/

/-- `Cn·μ/V ≤ μ²/64` from the gate `64·Cn ≤ μ·V`. -/
private lemma wCnMuDiv {V μ Cn : ℝ} (hV : 0 < V) (hμ : 0 ≤ μ)
    (hμV : 64 * Cn ≤ μ * V) : Cn * μ / V ≤ μ ^ 2 / 64 := by
  rw [div_le_iff₀ hV]
  have h1 : μ * (64 * Cn) ≤ μ * (μ * V) := mul_le_mul_of_nonneg_left hμV hμ
  have h2 : μ ^ 2 / 64 * V = μ ^ 2 * V / 64 := by ring
  nlinarith [h1, h2]

/-- `μ/V ≤ μ²/64` from `64 ≤ μ·V`. -/
private lemma wMuDiv {V μ : ℝ} (hV : 0 < V) (hμ : 0 ≤ μ)
    (h64 : 64 ≤ μ * V) : μ / V ≤ μ ^ 2 / 64 := by
  rw [div_le_iff₀ hV]
  have h1 : μ * 64 ≤ μ * (μ * V) := mul_le_mul_of_nonneg_left h64 hμ
  have h2 : μ ^ 2 / 64 * V = μ ^ 2 * V / 64 := by ring
  nlinarith [h1, h2]

/-! ## §2. The seven rows -/

/-- **Row 1**: `M₁(S/V)/V ≤ M₁μ²/32` from `S ≤ 2·Cn·μ·V` and `Cn·μ/V ≤ μ²/64`. -/
private lemma wrow_one {V μ M₁ S Cn : ℝ} (hV : 0 < V) (hM1 : 0 ≤ M₁)
    (hkey : Cn * μ / V ≤ μ ^ 2 / 64) (hS : S ≤ 2 * Cn * μ * V) :
    M₁ * (S / V) / V ≤ M₁ * μ ^ 2 / 32 := by
  have hSdivV : S / V ≤ 2 * Cn * μ := by
    rw [div_le_iff₀ hV]; linarith
  have h1 : M₁ * (S / V) ≤ M₁ * (2 * Cn * μ) := mul_le_mul_of_nonneg_left hSdivV hM1
  have h2 : M₁ * (S / V) / V ≤ M₁ * (2 * Cn * μ) / V :=
    div_le_div_of_nonneg_right h1 hV.le
  have h3 : M₁ * (Cn * μ / V) ≤ M₁ * (μ ^ 2 / 64) := mul_le_mul_of_nonneg_left hkey hM1
  have e : M₁ * (2 * Cn * μ) / V = 2 * (M₁ * (Cn * μ / V)) := by ring
  have e2 : M₁ * μ ^ 2 / 32 = 2 * (M₁ * (μ ^ 2 / 64)) := by ring
  linarith [h2, e, h3, e2]

/-- **Row 2**: the chemical-potential row `μM₁/(2V) ≤ M₁μ²/128` from `μ/V ≤ μ²/64`. -/
private lemma wrow_two {V μ M₁ : ℝ} (hM1 : 0 ≤ M₁)
    (hkey : μ / V ≤ μ ^ 2 / 64) : μ * M₁ / (2 * V) ≤ M₁ * μ ^ 2 / 128 := by
  have h1 : M₁ * (μ / V) ≤ M₁ * (μ ^ 2 / 64) := mul_le_mul_of_nonneg_left hkey hM1
  have e : μ * M₁ / (2 * V) = (1 / 2) * (M₁ * (μ / V)) := by ring
  have e2 : M₁ * μ ^ 2 / 128 = (1 / 2) * (M₁ * (μ ^ 2 / 64)) := by ring
  linarith [h1, e, e2]

/-- **Row 3**: the zero-point row `M₁/(4V²) ≤ M₁μ²/128` from `64 ≤ μV`. -/
private lemma wrow_three {V μ M₁ : ℝ} (hV : 0 < V) (hM1 : 0 ≤ M₁)
    (h64 : 64 ≤ μ * V) : M₁ / (4 * V ^ 2) ≤ M₁ * μ ^ 2 / 128 := by
  have hV2pos : (0 : ℝ) < 4 * V ^ 2 := by nlinarith
  have hsq : (64 : ℝ) ^ 2 ≤ (μ * V) ^ 2 := pow_le_pow_left₀ (by norm_num) h64 2
  have h32 : (32 : ℝ) ≤ μ ^ 2 * V ^ 2 := by nlinarith [hsq]
  have hinv : 1 / (4 * V ^ 2) ≤ μ ^ 2 / 128 := by
    rw [div_le_iff₀ hV2pos]
    have e : μ ^ 2 / 128 * (4 * V ^ 2) = μ ^ 2 * V ^ 2 / 32 := by ring
    linarith [h32, e]
  have h1 : M₁ * (1 / (4 * V ^ 2)) ≤ M₁ * (μ ^ 2 / 128) := mul_le_mul_of_nonneg_left hinv hM1
  have e1 : M₁ * (1 / (4 * V ^ 2)) = M₁ / (4 * V ^ 2) := by ring
  have e2 : M₁ * (μ ^ 2 / 128) = M₁ * μ ^ 2 / 128 := by ring
  linarith [h1, e1, e2]

/-- **Row 4**: `½(1+κΓ)G((n/V)/V) ≤ 9M₁μ²/256` from `κΓ ≤ 1/8`, `G ≤ 2M₁`, `n/V ≤ 2Cnμ`,
`Cn·μ/V ≤ μ²/64`. -/
private lemma wrow_four {V μ κ Γ G M₁ n Cn : ℝ} (hV : 0 < V) (hM1 : 0 ≤ M₁) (hG : 0 ≤ G)
    (hGle : G ≤ 2 * M₁) (hκΓ : κ * Γ ≤ 1 / 8) (hκ : 0 ≤ κ) (hΓ : 0 ≤ Γ)
    (hn : 0 ≤ n) (h2Cn : n / V ≤ 2 * Cn * μ) (hkey : Cn * μ / V ≤ μ ^ 2 / 64) :
    (1 / 2) * (1 + κ * Γ) * G * ((n / V) / V) ≤ 9 * M₁ * μ ^ 2 / 256 := by
  have hfac : (1 / 2) * (1 + κ * Γ) * G ≤ (9 / 8) * M₁ := by
    nlinarith [hκΓ, hGle, hG, hκ, hΓ, hM1]
  have hdivnV : (n / V) / V ≤ 2 * Cn * μ / V := by
    have h1 : (n / V) * (1 / V) ≤ (2 * Cn * μ) * (1 / V) :=
      mul_le_mul_of_nonneg_right h2Cn (div_nonneg zero_le_one hV.le)
    have e1 : (n / V) / V = (n / V) * (1 / V) := by ring
    have e2 : (2 * Cn * μ) * (1 / V) = 2 * Cn * μ / V := by ring
    linarith
  have hdiv0 : 0 ≤ (n / V) / V := div_nonneg (div_nonneg hn hV.le) hV.le
  have hb0 : 0 ≤ (9 / 8) * M₁ := by linarith
  have h1 : (1 / 2) * (1 + κ * Γ) * G * ((n / V) / V)
      ≤ (9 / 8) * M₁ * (2 * Cn * μ / V) := mul_le_mul hfac hdivnV hdiv0 hb0
  have h2 : (9 / 8) * M₁ * (2 * Cn * μ / V) = (9 / 4) * (M₁ * (Cn * μ / V)) := by ring
  have h3 : M₁ * (Cn * μ / V) ≤ M₁ * (μ ^ 2 / 64) := mul_le_mul_of_nonneg_left hkey hM1
  have h4 : (0 : ℝ) ≤ 9 / 4 := by norm_num
  have h5 : (9 / 4) * (M₁ * (Cn * μ / V)) ≤ (9 / 4) * (M₁ * (μ ^ 2 / 64)) :=
    mul_le_mul_of_nonneg_left h3 h4
  have e : 9 * M₁ * μ ^ 2 / 256 = (9 / 4) * (M₁ * (μ ^ 2 / 64)) := by ring
  linarith [h1, h2, h5, e]

/-- **Row 5**: `½(1−KK·2Γ)G(S/V)/V ≤ M₁μ²/32` from `KK·2Γ ≤ 1/2`, `G ≤ 2M₁`,
`S ≤ 2Cn·μ·V`, `Cn·μ/V ≤ μ²/64`. -/
private lemma wrow_five {V μ S G M₁ KK Γ Cn : ℝ} (hV : 0 < V) (hM1 : 0 ≤ M₁) (hG : 0 ≤ G)
    (hGle : G ≤ 2 * M₁) (hKKδ : KK * (2 * Γ) ≤ 1 / 2) (hKK0 : 0 ≤ KK) (hΓ : 0 ≤ Γ)
    (hS : 0 ≤ S) (hS2Cn : S ≤ 2 * Cn * μ * V) (hkey : Cn * μ / V ≤ μ ^ 2 / 64) :
    (1 / 2) * (1 - KK * (2 * Γ)) * G * (S / V) / V ≤ M₁ * μ ^ 2 / 32 := by
  have hfac : (1 / 2) * (1 - KK * (2 * Γ)) * G ≤ M₁ := by
    have h4 : (1 / 2) * (1 - KK * (2 * Γ)) ≤ 1 / 2 := by
      nlinarith [hKKδ, mul_nonneg hKK0 (by linarith : (0 : ℝ) ≤ 2 * Γ)]
    have h6 : (1 / 2) * (1 - KK * (2 * Γ)) * G ≤ (1 / 2) * G :=
      mul_le_mul_of_nonneg_right h4 hG
    have h7 : (1 / 2) * G ≤ M₁ := by linarith
    linarith
  have hSdivV : S / V ≤ 2 * Cn * μ := by
    rw [div_le_iff₀ hV]; linarith
  have hdivSV : (S / V) / V ≤ 2 * Cn * μ / V := by
    have h1 : (S / V) * (1 / V) ≤ (2 * Cn * μ) * (1 / V) :=
      mul_le_mul_of_nonneg_right hSdivV (div_nonneg zero_le_one hV.le)
    have e1 : (S / V) / V = (S / V) * (1 / V) := by ring
    have e2 : (2 * Cn * μ) * (1 / V) = 2 * Cn * μ / V := by ring
    linarith
  have hSVV0 : 0 ≤ (S / V) / V := div_nonneg (div_nonneg hS hV.le) hV.le
  have h1 : (1 / 2) * (1 - KK * (2 * Γ)) * G * ((S / V) / V) ≤ M₁ * (2 * Cn * μ / V) :=
    mul_le_mul hfac hdivSV hSVV0 hM1
  have h3 : M₁ * (Cn * μ / V) ≤ M₁ * (μ ^ 2 / 64) := mul_le_mul_of_nonneg_left hkey hM1
  have h4 : M₁ * (2 * Cn * μ / V) = 2 * (M₁ * (Cn * μ / V)) := by ring
  have e1 : (1 / 2) * (1 - KK * (2 * Γ)) * G * (S / V) / V
      = (1 / 2) * (1 - KK * (2 * Γ)) * G * ((S / V) / V) := by ring
  have e3 : M₁ * μ ^ 2 / 32 = 2 * (M₁ * (μ ^ 2 / 64)) := by ring
  linarith [h1, e1, h4, h3, e3]

/-- **Row 6**: `½G(2KK+κ)Γ(n/V)² ≤ M₁μ²/32` from `128·Cn²(2+κ)Γ ≤ 1`, `G ≤ 2M₁`, `KK ≤ 1`,
`0 ≤ n/V ≤ 2Cn·μ`. -/
private lemma wrow_six {V μ κ Γ KK G M₁ n Cn : ℝ} (hM1 : 0 ≤ M₁) (hG : 0 ≤ G)
    (hGle : G ≤ 2 * M₁) (hKK0 : 0 ≤ KK) (hKK1 : KK ≤ 1) (hκ : 0 ≤ κ) (hΓ : 0 ≤ Γ)
    (hΓrow : 128 * Cn ^ 2 * (2 + κ) * Γ ≤ 1) (hr0 : 0 ≤ n / V) (h2Cn : n / V ≤ 2 * Cn * μ)
    (hCn0 : 0 < Cn) :
    (1 / 2) * G * (2 * KK + κ) * Γ * (n / V) ^ 2 ≤ M₁ * μ ^ 2 / 32 := by
  have hG2 : (1 / 2) * G ≤ M₁ := by linarith
  have hden : (0 : ℝ) < 128 * Cn ^ 2 := by positivity
  have hΓle : (2 + κ) * Γ ≤ 1 / (128 * Cn ^ 2) := by
    rw [le_div_iff₀ hden]; linarith
  have hKG : (2 * KK + κ) * Γ ≤ 1 / (128 * Cn ^ 2) := by
    have h1 : 2 * KK + κ ≤ 2 + κ := by linarith
    have h2 : (2 * KK + κ) * Γ ≤ (2 + κ) * Γ := mul_le_mul_of_nonneg_right h1 hΓ
    linarith
  have hKG0 : 0 ≤ (2 * KK + κ) * Γ := mul_nonneg (by linarith) hΓ
  have hAR : (1 / 2) * G * ((2 * KK + κ) * Γ) ≤ M₁ * (1 / (128 * Cn ^ 2)) :=
    mul_le_mul hG2 hKG hKG0 hM1
  have hsq' : (2 * Cn * μ) ^ 2 = 4 * Cn ^ 2 * μ ^ 2 := by ring
  have hsq : (n / V) ^ 2 ≤ 4 * Cn ^ 2 * μ ^ 2 := by
    rw [← hsq']; exact pow_le_pow_left₀ hr0 h2Cn 2
  have hsq0 : 0 ≤ (n / V) ^ 2 := sq_nonneg _
  have hRHS0 : 0 ≤ M₁ * (1 / (128 * Cn ^ 2)) :=
    mul_nonneg hM1 (by positivity)
  have hABC : (1 / 2) * G * ((2 * KK + κ) * Γ) * ((n / V) ^ 2)
      ≤ M₁ * (1 / (128 * Cn ^ 2)) * (4 * Cn ^ 2 * μ ^ 2) :=
    mul_le_mul hAR hsq hsq0 hRHS0
  have e : (1 / 2) * G * (2 * KK + κ) * Γ * (n / V) ^ 2
      = (1 / 2) * G * ((2 * KK + κ) * Γ) * ((n / V) ^ 2) := by ring
  have e2 : M₁ * (1 / (128 * Cn ^ 2)) * (4 * Cn ^ 2 * μ ^ 2) = M₁ * μ ^ 2 / 32 := by
    field_simp; ring
  linarith [hABC, e, e2]

/-- **Row 7**: `Ca(c₀³(n/V)χ) ≤ (1/20)·(μ²M₁)` from `2c₀³(n/V)χ ≤ μ²ΓM₁` and
`Γ ≤ 1/(10(Ca+1))`.  The sign of `Ca` is handled by a case split. -/
private lemma wrow_seven {V μ a χ c₀ Γ C n M₁ : ℝ} (hV : 0 < V) (hM1 : 0 ≤ M₁)
    (hΓ : 0 ≤ Γ) (hχ : 0 ≤ χ) (hc0 : 0 ≤ c₀) (hn : 0 ≤ n)
    (hR3 : 2 * c₀ ^ 3 * (n / V) * χ ≤ μ ^ 2 * Γ * M₁)
    (hΓCaT : Γ ≤ 1 / (10 * (C * a + 1))) :
    C * a * (c₀ ^ 3 * (n / V) * χ) ≤ (1 / 20) * (μ ^ 2 * M₁) := by
  have hr0 : 0 ≤ n / V := div_nonneg hn hV.le
  have hX0 : 0 ≤ c₀ ^ 3 * (n / V) * χ :=
    mul_nonneg (mul_nonneg (pow_nonneg hc0 3) hr0) hχ
  have hXle : c₀ ^ 3 * (n / V) * χ ≤ (1 / 2) * (μ ^ 2 * Γ * M₁) := by linarith
  have hY0 : 0 ≤ (1 / 20) * (μ ^ 2 * M₁) :=
    mul_nonneg (by norm_num) (mul_nonneg (sq_nonneg μ) hM1)
  have hcaΓ : C * a * Γ ≤ 1 / 10 := by
    by_cases hKl : 0 < 10 * (C * a + 1)
    · have h1 : Γ * (10 * (C * a + 1)) ≤ 1 := by
        rw [le_div_iff₀ hKl] at hΓCaT; exact hΓCaT
      nlinarith [h1, hΓ]
    · have h1 : 10 * (C * a + 1) ≤ 0 := not_lt.mp hKl
      have h2 : 1 / (10 * (C * a + 1)) ≤ 0 :=
        div_nonpos_of_nonneg_of_nonpos (by norm_num) h1
      have h3 : Γ = 0 := le_antisymm (le_trans hΓCaT h2) hΓ
      rw [h3]; norm_num
  by_cases hca : 0 ≤ C * a
  · have h1 : C * a * (c₀ ^ 3 * (n / V) * χ) ≤ C * a * ((1 / 2) * (μ ^ 2 * Γ * M₁)) :=
      mul_le_mul_of_nonneg_left hXle hca
    have hY1 : 0 ≤ (1 / 2) * (μ ^ 2 * M₁) :=
      mul_nonneg (by norm_num) (mul_nonneg (sq_nonneg μ) hM1)
    have h2a : (C * a * Γ) * ((1 / 2) * (μ ^ 2 * M₁)) ≤ (1 / 10) * ((1 / 2) * (μ ^ 2 * M₁)) :=
      mul_le_mul_of_nonneg_right hcaΓ hY1
    have e : C * a * ((1 / 2) * (μ ^ 2 * Γ * M₁))
        = (C * a * Γ) * ((1 / 2) * (μ ^ 2 * M₁)) := by ring
    have e2 : (1 / 10) * ((1 / 2) * (μ ^ 2 * M₁)) = (1 / 20) * (μ ^ 2 * M₁) := by ring
    linarith
  · have h1 : C * a ≤ 0 := (not_le.mp hca).le
    have h2 : C * a * (c₀ ^ 3 * (n / V) * χ) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg h1 hX0
    linarith

/-- **The wide small-rows bundle.**  The seven rows of the cube ledger, with the density window
`4μ ≤ n/V ≤ 2·Cn·μ` (arbitrary `Cn ≥ 4`) and the box-volume gate `64·Cn ≤ μ·V`.

This is the PROVED `Work.BoseB1Cube.smallRowsBundle` with `n/V ≤ 5μ` and `64 ≤ μV` replaced by the
`Cn`-scaled hypotheses.  PROOF RECIPE: copy the proof of `smallRowsBundle` term by term, using
`μ V ≥ 64*Cn` in place of `μ V ≥ 64`; the seven row bounds become

* `M₁(S/V)/V ≤ M₁t/V ≤ M₁·2Cn μ/V ≤ M₁μ²/32`,
* `μM₁/(2V) ≤ M₁μ²/128`,
* `M₁/(4V²) ≤ M₁μ²/128`,
* `½(1+κΓ)G((n/V)/V) ≤ (9/8)·2M₁·2Cn μ/V ≤ 9M₁μ²/256`,
* `½(1−KK·2Γ)G(S/V)/V ≤ 2M₁·t/V ≤ M₁μ²/32`,
* `½G(2KK+κ)Γ(n/V)² ≤ 4M₁Cn²(2+κ)Γμ² ≤ M₁μ²/32` (this is the hypothesis `hΓrow`),
* `C a (c₀³(n/V)χ) ≤ ½·C a·μ²Γ M₁ = (C a Γ)μ²M₁/2 ≤ (1/20)μ²M₁` (from `hR3` and `C a Γ ≤ 1/10`
  from `hΓCaT`, case-splitting on `0 ≤ C*a` as in `smallRowsBundle`'s `row_seven`; this is the row
  whose constant is 1/20, **not** 1/32),

whose sum is `≤ (1/2)μ²M₁` (total coefficient ≈ 0.26); the middle rows also use `S ≤ n` (from
`hSQ`), `G ≤ 2M₁`, `κΓ ≤ 1/8`, `KK(2Γ) ≤ 1/2`, and `Cn ≥ 4`. -/
theorem smallRowsBundleWide {V μ a χ G M₁ S Q c₀ Γ κ KK C n Cn : ℝ}
    (hV : 0 < V) (hμ : 0 < μ) (hΓ : 0 ≤ Γ) (hκ : 0 ≤ κ) (hC : 0 ≤ C)
    (hM1 : 0 ≤ M₁) (hG : 0 ≤ G) (hS : 0 ≤ S) (hQ : 0 ≤ Q) (hχ : 0 ≤ χ) (hc0 : 0 ≤ c₀)
    (hn : 0 ≤ n) (hCn : 4 ≤ Cn) (hSQ : S + Q = (n / V) * V)
    (h4 : 4 * μ ≤ n / V) (h2Cn : n / V ≤ 2 * Cn * μ)
    (hμV : 64 * Cn ≤ μ * V) (hKK0 : 0 ≤ KK) (hKK1 : KK ≤ 1)
    (hKKδ : KK * (2 * Γ) ≤ 1 / 2) (hκΓ : κ * Γ ≤ 1 / 8) (hGle : G ≤ 2 * M₁)
    (hR3 : 2 * c₀ ^ 3 * (n / V) * χ ≤ μ ^ 2 * Γ * M₁)
    (hΓCaT : Γ ≤ 1 / (10 * (C * a + 1))) (hΓrow : 128 * Cn ^ 2 * (2 + κ) * Γ ≤ 1) :
    M₁ * (S / V) / V + μ * M₁ / (2 * V) + M₁ / (4 * V ^ 2)
      + (1 / 2) * (1 + κ * Γ) * G * ((n / V) / V)
      + (1 / 2) * (1 - KK * (2 * Γ)) * G * (S / V) / V
      + (1 / 2) * G * (2 * KK + κ) * Γ * (n / V) ^ 2
      + C * a * (c₀ ^ 3 * (n / V) * χ)
      ≤ (1 / 2) * μ ^ 2 * M₁ := by
  have hCn0 : (0 : ℝ) < Cn := by linarith
  have hrV : (n / V) * V = n := by field_simp
  have hSQn : S + Q = n := by rw [hSQ, hrV]
  have hSlen : S ≤ n := by linarith
  have hr0 : 0 ≤ n / V := div_nonneg hn hV.le
  have hn2CnV : n ≤ 2 * Cn * μ * V := by
    have h1 : (n / V) * V ≤ (2 * Cn * μ) * V := mul_le_mul_of_nonneg_right h2Cn hV.le
    linarith [h1, hrV]
  have hS2CnV : S ≤ 2 * Cn * μ * V := by linarith
  have h64 : (64 : ℝ) ≤ μ * V := by nlinarith
  have hkey1 : Cn * μ / V ≤ μ ^ 2 / 64 := wCnMuDiv hV hμ.le hμV
  have hkey2 : μ / V ≤ μ ^ 2 / 64 := wMuDiv hV hμ.le h64
  have hY0 : 0 ≤ μ ^ 2 * M₁ := mul_nonneg (sq_nonneg μ) hM1
  have hA : M₁ * (S / V) / V ≤ M₁ * μ ^ 2 / 32 :=
    wrow_one hV hM1 hkey1 hS2CnV
  have hB : μ * M₁ / (2 * V) ≤ M₁ * μ ^ 2 / 128 := wrow_two hM1 hkey2
  have hC' : M₁ / (4 * V ^ 2) ≤ M₁ * μ ^ 2 / 128 := wrow_three hV hM1 h64
  have hD : (1 / 2) * (1 + κ * Γ) * G * ((n / V) / V) ≤ 9 * M₁ * μ ^ 2 / 256 :=
    wrow_four hV hM1 hG hGle hκΓ hκ hΓ hn h2Cn hkey1
  have hE : (1 / 2) * (1 - KK * (2 * Γ)) * G * (S / V) / V ≤ M₁ * μ ^ 2 / 32 :=
    wrow_five hV hM1 hG hGle hKKδ hKK0 hΓ hS hS2CnV hkey1
  have hF : (1 / 2) * G * (2 * KK + κ) * Γ * (n / V) ^ 2 ≤ M₁ * μ ^ 2 / 32 :=
    wrow_six hM1 hG hGle hKK0 hKK1 hκ hΓ hΓrow hr0 h2Cn hCn0
  have hG7 : C * a * (c₀ ^ 3 * (n / V) * χ) ≤ (1 / 20) * (μ ^ 2 * M₁) :=
    wrow_seven hV hM1 hΓ hχ hc0 hn hR3 hΓCaT
  linarith only [hA, hB, hC', hD, hE, hF, hG7, hY0]

end Work.BoseB1Cube
