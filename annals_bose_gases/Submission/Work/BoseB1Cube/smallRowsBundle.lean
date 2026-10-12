import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseB1Cube.shiftR3Row
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseB1Cube

set_option maxHeartbeats 1000000
set_option linter.unusedVariables false

/-!
# `Work.BoseB1Cube.smallRowsBundle`

A pure real-arithmetic bundle: the seven rows of the cube ledger all fit under the manifest
margin `½ μ² M₁`, given the diluteness window `4μ ≤ n/V ≤ 5μ`, `64 ≤ μV`, the smallness of
`Γ` (`Γ(2+κ) ≤ 1/500`, `Γ ≤ 1/(10(Ca+1))`), the pair-condensate gate `KK·2Γ ≤ 1/2`, the
kinetic cap `κΓ ≤ 1/8`, the mass gate `G ≤ 2M₁` and the row `2c₀³(n/V)χ ≤ μ²ΓM₁`.

The proof is a term-by-term comparison; each row is isolated in its own small lemma so that the
arithmetic tactics see a minimal context.  Every bound is stated against the *same* normalised
monomial `M₁·μ/V` (resp. `μ²·M₁`) that occurs in the target, which is what lets the final
`linarith` combine the seven rows.
-/

/-- **Row 1**: `M₁(S/V)/V ≤ 5·(M₁μ/V)` from `S ≤ 5μV`. -/
private lemma row_one {V μ M₁ S : ℝ} (hV : 0 < V) (hM1 : 0 ≤ M₁) (hS : S ≤ 5 * μ * V) :
    M₁ * (S / V) / V ≤ 5 * (M₁ * μ / V) := by
  have hSdivV : S / V ≤ 5 * μ := by
    rw [div_le_iff₀ hV]; linarith
  have h1 : M₁ * (S / V) ≤ M₁ * (5 * μ) := mul_le_mul_of_nonneg_left hSdivV hM1
  have h2 : M₁ * (S / V) / V ≤ M₁ * (5 * μ) / V := div_le_div_of_nonneg_right h1 hV.le
  have h3 : M₁ * (5 * μ) / V = 5 * (M₁ * μ / V) := by ring
  linarith

/-- **Row 2**: the chemical-potential row `μM₁/(2V) = ½·(M₁μ/V)`. -/
private lemma row_two {V μ M₁ : ℝ} :
    μ * M₁ / (2 * V) ≤ (1 / 2) * (M₁ * μ / V) := by
  have h1 : μ * M₁ / (2 * V) = (1 / 2) * (M₁ * μ / V) := by ring
  linarith

/-- **Row 3**: the zero-point row `M₁/(4V²) ≤ M₁μ/V` from `64 ≤ μV`. -/
private lemma row_three {V μ M₁ : ℝ} (hV : 0 < V) (hM1 : 0 ≤ M₁) (hμV : 64 ≤ μ * V) :
    M₁ / (4 * V ^ 2) ≤ M₁ * μ / V := by
  have hV2pos : (0 : ℝ) < 4 * V ^ 2 := by nlinarith
  have hVinv2 : 1 / (4 * V ^ 2) ≤ μ / V := by
    rw [div_le_iff₀ hV2pos]
    have h1 : μ / V * (4 * V ^ 2) = 4 * μ * V := by field_simp
    rw [h1]; nlinarith
  have h1 : M₁ * (1 / (4 * V ^ 2)) ≤ M₁ * (μ / V) := mul_le_mul_of_nonneg_left hVinv2 hM1
  have e1 : M₁ * (1 / (4 * V ^ 2)) = M₁ / (4 * V ^ 2) := by ring
  have e2 : M₁ * (μ / V) = M₁ * μ / V := by ring
  linarith

/-- **Row 4**: `½(1+κΓ)G((n/V)/V) ≤ (45/8)·(M₁μ/V)` from `κΓ ≤ 1/8`, `G ≤ 2M₁`, `n/V ≤ 5μ`. -/
private lemma row_four {V μ κ Γ G M₁ n : ℝ} (hV : 0 < V) (hM1 : 0 ≤ M₁) (hG : 0 ≤ G)
    (hGle : G ≤ 2 * M₁) (hκΓ : κ * Γ ≤ 1 / 8) (hκ : 0 ≤ κ) (hΓ : 0 ≤ Γ)
    (hn : 0 ≤ n) (h5 : n / V ≤ 5 * μ) :
    (1 / 2) * (1 + κ * Γ) * G * ((n / V) / V) ≤ (45 / 8) * (M₁ * μ / V) := by
  have hfac : (1 / 2) * (1 + κ * Γ) * G ≤ (9 / 8) * M₁ := by
    nlinarith [hκΓ, hGle, hG, hκ, hΓ, hM1]
  have hdivnV : (n / V) / V ≤ 5 * μ / V := by
    have h1 : (n / V) * (1 / V) ≤ (5 * μ) * (1 / V) :=
      mul_le_mul_of_nonneg_right h5 (div_nonneg zero_le_one hV.le)
    have e1 : (n / V) / V = (n / V) * (1 / V) := by ring
    have e2 : (5 * μ) * (1 / V) = 5 * μ / V := by ring
    linarith
  have hdiv0 : 0 ≤ (n / V) / V := div_nonneg (div_nonneg hn hV.le) hV.le
  have hb0 : 0 ≤ (9 / 8) * M₁ := by linarith
  have h1 : (1 / 2) * (1 + κ * Γ) * G * ((n / V) / V) ≤ (9 / 8) * M₁ * (5 * μ / V) :=
    mul_le_mul hfac hdivnV hdiv0 hb0
  have e : (9 / 8) * M₁ * (5 * μ / V) = (45 / 8) * (M₁ * μ / V) := by ring
  linarith

/-- **Row 5**: `½(1-KK·2Γ)G(S/V)/V ≤ 5·(M₁μ/V)` from `KK·2Γ ≤ 1/2`, `G ≤ 2M₁`, `S ≤ 5μV`. -/
private lemma row_five {V μ S G M₁ KK Γ : ℝ} (hV : 0 < V) (hM1 : 0 ≤ M₁) (hG : 0 ≤ G)
    (hGle : G ≤ 2 * M₁) (hKKδ : KK * (2 * Γ) ≤ 1 / 2) (hKK0 : 0 ≤ KK) (hΓ : 0 ≤ Γ)
    (hS : 0 ≤ S) (hS5 : S ≤ 5 * μ * V) :
    (1 / 2) * (1 - KK * (2 * Γ)) * G * (S / V) / V ≤ 5 * (M₁ * μ / V) := by
  have hK0 : 0 ≤ 1 - KK * (2 * Γ) := by nlinarith [hKKδ]
  have hfac : (1 / 2) * (1 - KK * (2 * Γ)) * G ≤ M₁ := by
    have h4 : (1 / 2) * (1 - KK * (2 * Γ)) ≤ 1 / 2 := by
      nlinarith [hKKδ, mul_nonneg hKK0 (by linarith : (0:ℝ) ≤ 2 * Γ)]
    have h6 : (1 / 2) * (1 - KK * (2 * Γ)) * G ≤ (1 / 2) * G :=
      mul_le_mul_of_nonneg_right h4 hG
    have h7 : (1 / 2) * G ≤ M₁ := by linarith
    linarith
  have hSdivV : S / V ≤ 5 * μ := by
    rw [div_le_iff₀ hV]; linarith
  have hdivSV : (S / V) / V ≤ 5 * μ / V := by
    have h1 : (S / V) * (1 / V) ≤ (5 * μ) * (1 / V) :=
      mul_le_mul_of_nonneg_right hSdivV (div_nonneg zero_le_one hV.le)
    have e1 : (S / V) / V = (S / V) * (1 / V) := by ring
    have e2 : (5 * μ) * (1 / V) = 5 * μ / V := by ring
    linarith
  have hSVV0 : 0 ≤ (S / V) / V := div_nonneg (div_nonneg hS hV.le) hV.le
  have h1 : (1 / 2) * (1 - KK * (2 * Γ)) * G * ((S / V) / V) ≤ M₁ * (5 * μ / V) :=
    mul_le_mul hfac hdivSV hSVV0 hM1
  have e1 : (1 / 2) * (1 - KK * (2 * Γ)) * G * (S / V) / V
      = (1 / 2) * (1 - KK * (2 * Γ)) * G * ((S / V) / V) := by ring
  have e2 : M₁ * (5 * μ / V) = 5 * (M₁ * μ / V) := by ring
  linarith

/-- **Row 6**: `½G(2KK+κ)Γ(n/V)² ≤ (1/20)·(μ²M₁)` from `(2+κ)Γ ≤ 1/500`, `G ≤ 2M₁`,
`0 ≤ n/V ≤ 5μ`. -/
private lemma row_six {V μ κ Γ KK G M₁ n : ℝ} (hV : 0 < V) (hM1 : 0 ≤ M₁) (hG : 0 ≤ G)
    (hGle : G ≤ 2 * M₁) (hKK0 : 0 ≤ KK) (hKK1 : KK ≤ 1) (hκ : 0 ≤ κ) (hΓ : 0 ≤ Γ)
    (hΓrow : (2 + κ) * Γ ≤ 1 / 500) (hr0 : 0 ≤ n / V) (h5 : n / V ≤ 5 * μ) :
    (1 / 2) * G * (2 * KK + κ) * Γ * (n / V) ^ 2 ≤ (1 / 20) * (μ ^ 2 * M₁) := by
  have hG2 : (1 / 2) * G ≤ M₁ := by linarith
  have hsq : (n / V) ^ 2 ≤ 25 * μ ^ 2 := by
    have h := pow_le_pow_left₀ hr0 h5 2
    nlinarith
  have hKG : (2 * KK + κ) * Γ ≤ 1 / 500 := by
    have h1 : 2 * KK + κ ≤ 2 + κ := by linarith
    have h2 : (2 * KK + κ) * Γ ≤ (2 + κ) * Γ := mul_le_mul_of_nonneg_right h1 hΓ
    linarith
  have hKG0 : 0 ≤ (2 * KK + κ) * Γ := mul_nonneg (by linarith) hΓ
  have hsq0 : 0 ≤ (n / V) ^ 2 := sq_nonneg _
  have hAB : (1 / 2) * G * ((2 * KK + κ) * Γ) ≤ M₁ * (1 / 500) :=
    mul_le_mul hG2 hKG hKG0 hM1
  have hRHS0 : 0 ≤ M₁ * (1 / 500) := mul_nonneg hM1 (by norm_num)
  have hABC : (1 / 2) * G * ((2 * KK + κ) * Γ) * ((n / V) ^ 2)
      ≤ M₁ * (1 / 500) * (25 * μ ^ 2) :=
    mul_le_mul hAB hsq hsq0 hRHS0
  have e : (1 / 2) * G * (2 * KK + κ) * Γ * (n / V) ^ 2
      = (1 / 2) * G * ((2 * KK + κ) * Γ) * ((n / V) ^ 2) := by ring
  have e2 : M₁ * (1 / 500) * (25 * μ ^ 2) = (1 / 20) * (μ ^ 2 * M₁) := by ring
  linarith

/-- **Row 7**: `Ca(c₀³(n/V)χ) ≤ (1/20)·(μ²M₁)` from `2c₀³(n/V)χ ≤ μ²ΓM₁` and
`Γ ≤ 1/(10(Ca+1))`.  The sign of `Ca` is handled by a case split. -/
private lemma row_seven {V μ a χ c₀ Γ C n M₁ : ℝ} (hV : 0 < V) (hM1 : 0 ≤ M₁)
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

theorem smallRowsBundle {V μ a χ G M₁ S Q c₀ Γ κ KK C n : ℝ}
    (hV : 0 < V) (hμ : 0 < μ) (hΓ : 0 ≤ Γ) (hκ : 0 ≤ κ) (hC : 0 ≤ C)
    (hM1 : 0 ≤ M₁) (hG : 0 ≤ G) (hS : 0 ≤ S) (hQ : 0 ≤ Q) (hχ : 0 ≤ χ) (hc0 : 0 ≤ c₀)
    (hn : 0 ≤ n) (hSQ : S + Q = (n / V) * V) (h4 : 4 * μ ≤ n / V) (h5 : n / V ≤ 5 * μ)
    (hμV : 64 ≤ μ * V) (hKK0 : 0 ≤ KK) (hKK1 : KK ≤ 1) (hKKδ : KK * (2 * Γ) ≤ 1 / 2)
    (hκΓ : κ * Γ ≤ 1 / 8) (hGle : G ≤ 2 * M₁)
    (hR3 : 2 * c₀ ^ 3 * (n / V) * χ ≤ μ ^ 2 * Γ * M₁)
    (hΓCaT : Γ ≤ 1 / (10 * (C * a + 1))) (hΓrow : (2 + κ) * Γ ≤ 1 / 500) :
    M₁ * (S / V) / V + μ * M₁ / (2 * V) + M₁ / (4 * V ^ 2)
      + (1 / 2) * (1 + κ * Γ) * G * ((n / V) / V)
      + (1 / 2) * (1 - KK * (2 * Γ)) * G * (S / V) / V
      + (1 / 2) * G * (2 * KK + κ) * Γ * (n / V) ^ 2
      + C * a * (c₀ ^ 3 * (n / V) * χ)
      ≤ (1 / 2) * μ ^ 2 * M₁ := by
  have hrV : (n / V) * V = n := by field_simp
  have hSQn : S + Q = n := by rw [hSQ, hrV]
  have hSlen : S ≤ n := by linarith
  have hr0 : 0 ≤ n / V := div_nonneg hn hV.le
  have hn5 : n ≤ 5 * μ * V := by
    have h1 : (n / V) * V ≤ (5 * μ) * V := mul_le_mul_of_nonneg_right h5 hV.le
    nlinarith
  have hS5 : S ≤ 5 * μ * V := by linarith
  have hX0 : 0 ≤ M₁ * μ / V := div_nonneg (mul_nonneg hM1 hμ.le) hV.le
  have hY0 : 0 ≤ μ ^ 2 * M₁ := mul_nonneg (sq_nonneg μ) hM1
  have hA : M₁ * (S / V) / V ≤ 5 * (M₁ * μ / V) := row_one hV hM1 hS5
  have hB : μ * M₁ / (2 * V) ≤ (1 / 2) * (M₁ * μ / V) := row_two
  have hC : M₁ / (4 * V ^ 2) ≤ M₁ * μ / V := row_three hV hM1 hμV
  have hD : (1 / 2) * (1 + κ * Γ) * G * ((n / V) / V) ≤ (45 / 8) * (M₁ * μ / V) :=
    row_four hV hM1 hG hGle hκΓ hκ hΓ hn h5
  have hE : (1 / 2) * (1 - KK * (2 * Γ)) * G * (S / V) / V ≤ 5 * (M₁ * μ / V) :=
    row_five hV hM1 hG hGle hKKδ hKK0 hΓ hS hS5
  have hF : (1 / 2) * G * (2 * KK + κ) * Γ * (n / V) ^ 2 ≤ (1 / 20) * (μ ^ 2 * M₁) :=
    row_six hV hM1 hG hGle hKK0 hKK1 hκ hΓ hΓrow hr0 h5
  have hG7 : C * a * (c₀ ^ 3 * (n / V) * χ) ≤ (1 / 20) * (μ ^ 2 * M₁) :=
    row_seven hV hM1 hΓ hχ hc0 hn hR3 hΓCaT
  have hMkey : M₁ * μ / V ≤ μ ^ 2 * M₁ / 64 := by
    have hVinv : 1 / V ≤ μ / 64 := by
      rw [div_le_iff₀ hV]
      have h1 : μ / 64 * V = μ * V / 64 := by ring
      rw [h1]; linarith
    calc M₁ * μ / V = M₁ * μ * (1 / V) := by ring
      _ ≤ M₁ * μ * (μ / 64) := mul_le_mul_of_nonneg_left hVinv (mul_nonneg hM1 hμ.le)
      _ = μ ^ 2 * M₁ / 64 := by ring
  have hsum : M₁ * (S / V) / V + μ * M₁ / (2 * V) + M₁ / (4 * V ^ 2)
        + (1 / 2) * (1 + κ * Γ) * G * ((n / V) / V)
        + (1 / 2) * (1 - KK * (2 * Γ)) * G * (S / V) / V
        + (1 / 2) * G * (2 * KK + κ) * Γ * (n / V) ^ 2
        + C * a * (c₀ ^ 3 * (n / V) * χ)
        ≤ 18 * (M₁ * μ / V) + (1 / 10) * (μ ^ 2 * M₁) := by
    linarith only [hA, hB, hC, hD, hE, hF, hG7, hX0]
  have hkey2 : 18 * (M₁ * μ / V) + (1 / 10) * (μ ^ 2 * M₁) ≤ (1 / 2) * (μ ^ 2 * M₁) := by
    nlinarith only [hMkey, hY0]
  have e2 : (1 / 2) * (μ ^ 2 * M₁) = (1 / 2) * μ ^ 2 * M₁ := by ring
  linarith only [hsum, hkey2, e2]

end Work.BoseB1Cube
