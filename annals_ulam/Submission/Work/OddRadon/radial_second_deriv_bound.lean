import Mathlib

set_option maxHeartbeats 4000000

namespace Work.OddRadon

/-- Uniform lower bound for the coefficient of `R''` in the chord equation, on the box
`R, r ∈ [7/8, 9/8]`: `(2n+2)(2n+1) * 2 * (7/8)^{4n+1}` written without the `pow_add`
identification. -/
private noncomputable def radD (n : ℕ) : ℝ :=
  ((2*n+2 : ℕ) : ℝ) * ((2*n+1 : ℕ) : ℝ) *
    ((7/8 : ℝ) ^ (2*n+1) * (7/8 : ℝ) ^ (2*n) + (7/8 : ℝ) ^ (2*n) * (7/8 : ℝ) ^ (2*n+1))

/-- Uniform bound for the right-hand side of the chord equation, per unit of `ε`. -/
private noncomputable def radK (n : ℕ) (C₁ : ℝ) : ℝ :=
  ((2*n+1 : ℕ) : ℝ) * (9/8 : ℝ) ^ (2*n) *
      (1 + 2 * (((2*n+2 : ℕ) : ℝ) * (((2*n+1 : ℕ) : ℝ) * ((9/8 : ℝ) ^ (2*n) * C₁ ^ 2))))
    + ((2*n+2 : ℕ) : ℝ) * (9/8 : ℝ) ^ (2*n+1) *
      (1 + 2 * (((2*n+1 : ℕ) : ℝ) * (((2*n : ℕ) : ℝ) * ((9/8 : ℝ) ^ (2*n-1) * C₁ ^ 2))))

/-- `x * x ≤ C^2 * e` when `|x| ≤ C * e` and `e ≤ 1`, `e ≥ 0`. -/
private lemma sq_le_of_abs_le {x C e : ℝ} (he0 : 0 ≤ e) (he1 : e ≤ 1) (hx : |x| ≤ C * e) :
    x * x ≤ C ^ 2 * e := by
  have h1 : x * x ≤ (C * e) * (C * e) := by
    have h' : |x * x| ≤ (C * e) * (C * e) := by
      rw [abs_mul]
      exact mul_le_mul hx hx (abs_nonneg x) (le_trans (abs_nonneg x) hx)
    exact le_trans (le_abs_self (x * x)) h'
  have h2 : (C * e) * (C * e) ≤ C ^ 2 * e := by
    have h3 : 0 ≤ C ^ 2 * e := mul_nonneg (sq_nonneg C) he0
    have h4 : C ^ 2 * e * e ≤ C ^ 2 * e * 1 := mul_le_mul_of_nonneg_left he1 h3
    nlinarith [h4]
  linarith

/-- Absolute-value form of `sq_le_of_abs_le`. -/
private lemma abs_sq_le_of_abs_le {x C e : ℝ} (he0 : 0 ≤ e) (he1 : e ≤ 1) (hx : |x| ≤ C * e) :
    |x * x| ≤ C ^ 2 * e := by
  rw [abs_of_nonneg (mul_self_nonneg x)]
  exact sq_le_of_abs_le he0 he1 hx

/-- Key product estimate: if `|x| ≤ C₁ ε`, `0 ≤ P ≤ u`, `coef ≥ 0` and `ε ≤ 1`, then
`|coef * (P * x * x)| ≤ coef * (u * C₁^2) * ε`. -/
private lemma abs_coef_mul_le {coef P x C₁ ε u : ℝ} (hcoef : 0 ≤ coef) (hP0 : 0 ≤ P)
    (hPu : P ≤ u) (he0 : 0 ≤ ε) (he1 : ε ≤ 1) (hx : |x| ≤ C₁ * ε) :
    |coef * (P * x * x)| ≤ coef * (u * C₁ ^ 2) * ε := by
  have hp : |x * x| ≤ C₁ ^ 2 * ε := abs_sq_le_of_abs_le he0 he1 hx
  have hE : 0 ≤ C₁ ^ 2 * ε := mul_nonneg (sq_nonneg C₁) he0
  have heq : coef * (P * x * x) = (coef * P) * (x * x) := by ring
  rw [heq, abs_mul, abs_of_nonneg (mul_nonneg hcoef hP0)]
  calc (coef * P) * |x * x| ≤ (coef * P) * (C₁ ^ 2 * ε) :=
        mul_le_mul_of_nonneg_left hp (mul_nonneg hcoef hP0)
    _ ≤ (coef * u) * (C₁ ^ 2 * ε) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hPu hcoef) hE
    _ = coef * (u * C₁ ^ 2) * ε := by ring

/-- `radD n > 0`. -/
private lemma radD_pos (n : ℕ) : 0 < radD n := by
  rw [radD]
  exact mul_pos (by positivity) (by positivity)

/-- `radD n` is a lower bound for the coefficient of `R''`. -/
private lemma radD_le (n : ℕ) {R r : ℝ} (hR : (7/8 : ℝ) ≤ R) (hr : (7/8 : ℝ) ≤ r) :
    radD n ≤ ((2*n+2 : ℕ) : ℝ) * ((2*n+1 : ℕ) : ℝ) *
      (R ^ (2*n+1) * r ^ (2*n) + R ^ (2*n) * r ^ (2*n+1)) := by
  have hR0 : 0 ≤ R := by linarith
  have hr0 : 0 ≤ r := by linarith
  have hd : (0 : ℝ) ≤ 7/8 := by norm_num
  have h1 : (7/8 : ℝ) ^ (2*n+1) ≤ R ^ (2*n+1) := pow_le_pow_left₀ hd hR (2*n+1)
  have h2 : (7/8 : ℝ) ^ (2*n) ≤ r ^ (2*n) := pow_le_pow_left₀ hd hr (2*n)
  have h3 : (7/8 : ℝ) ^ (2*n) ≤ R ^ (2*n) := pow_le_pow_left₀ hd hR (2*n)
  have h4 : (7/8 : ℝ) ^ (2*n+1) ≤ r ^ (2*n+1) := pow_le_pow_left₀ hd hr (2*n+1)
  have ht1 : (7/8 : ℝ)^(2*n+1) * (7/8)^(2*n) ≤ R^(2*n+1) * r^(2*n) :=
    mul_le_mul h1 h2 (pow_nonneg hd _) (le_trans (pow_nonneg hd _) h1)
  have ht2 : (7/8 : ℝ)^(2*n) * (7/8)^(2*n+1) ≤ R^(2*n) * r^(2*n+1) :=
    mul_le_mul h3 h4 (pow_nonneg hd _) (le_trans (pow_nonneg hd _) h3)
  have hsum : (7/8 : ℝ)^(2*n+1) * (7/8)^(2*n) + (7/8)^(2*n) * (7/8)^(2*n+1)
      ≤ R^(2*n+1) * r^(2*n) + R^(2*n) * r^(2*n+1) := add_le_add ht1 ht2
  rw [radD]
  exact mul_le_mul_of_nonneg_left hsum (by positivity)

theorem radial_second_deriv_bound (n : ℕ) (hn : 1 ≤ n) (C₁ : ℝ) (hC₁ : 0 ≤ C₁) :
    ∃ C₂ : ℝ, 0 < C₂ ∧ ∀ {R r R' r' R'' a b ε : ℝ},
      7/8 ≤ R → R ≤ 9/8 → 7/8 ≤ r → r ≤ 9/8 → 0 ≤ ε → ε ≤ 1 →
      |R'| ≤ C₁ * ε → |r'| ≤ C₁ * ε → |a| < ε → |b| < ε →
      (((2*n+2 : ℕ) : ℝ) * ((2*n+1 : ℕ) : ℝ) * (R ^ (2*n+1) * r ^ (2*n) + R ^ (2*n) * r ^ (2*n+1))) * R''
        = ((2*n+1 : ℕ) : ℝ) * r ^ (2*n) * (a - (((2*n+2 : ℕ) : ℝ) * (((2*n+1 : ℕ) : ℝ) * R ^ (2*n) * R' * R') + ((2*n+2 : ℕ) : ℝ) * (((2*n+1 : ℕ) : ℝ) * r ^ (2*n) * r' * r')))
          + ((2*n+2 : ℕ) : ℝ) * r ^ (2*n+1) * (b - (((2*n+1 : ℕ) : ℝ) * (((2*n : ℕ) : ℝ) * R ^ (2*n-1) * R' * R') - (((2*n+1 : ℕ) : ℝ) * (((2*n : ℕ) : ℝ) * r ^ (2*n-1) * r' * r')))) →
      |R''| ≤ C₂ * ε := by
  refine ⟨(radK n C₁ + 1) / radD n, ?hpos, ?hmain⟩
  · have hKnn : 0 ≤ radK n C₁ := by rw [radK]; positivity
    exact div_pos (by linarith) (radD_pos n)
  · intro R r R' r' R'' a b ε hR1 hR2 hr1 hr2 hε0 hε1 hR' hr' ha hb heq
    set D : ℝ := ((2*n+2 : ℕ) : ℝ) * ((2*n+1 : ℕ) : ℝ) *
      (R ^ (2*n+1) * r ^ (2*n) + R ^ (2*n) * r ^ (2*n+1)) with hD
    set X1 : ℝ := ((2*n+2 : ℕ) : ℝ) * (((2*n+1 : ℕ) : ℝ) * R ^ (2*n) * R' * R') with hX1
    set X2 : ℝ := ((2*n+2 : ℕ) : ℝ) * (((2*n+1 : ℕ) : ℝ) * r ^ (2*n) * r' * r') with hX2
    set Y1 : ℝ := ((2*n+1 : ℕ) : ℝ) * (((2*n : ℕ) : ℝ) * R ^ (2*n-1) * R' * R') with hY1
    set Y2 : ℝ := ((2*n+1 : ℕ) : ℝ) * (((2*n : ℕ) : ℝ) * r ^ (2*n-1) * r' * r') with hY2
    set U1 : ℝ := (((2*n+2 : ℕ) : ℝ) * ((2*n+1 : ℕ) : ℝ)) *
      ((9/8 : ℝ) ^ (2*n) * C₁ ^ 2) with hU1
    set U2 : ℝ := (((2*n+1 : ℕ) : ℝ) * ((2*n : ℕ) : ℝ)) *
      ((9/8 : ℝ) ^ (2*n-1) * C₁ ^ 2) with hU2
    have hKeq : ((2*n+1 : ℕ) : ℝ) * (9/8 : ℝ) ^ (2*n) * (1 + 2 * U1)
        + ((2*n+2 : ℕ) : ℝ) * (9/8 : ℝ) ^ (2*n+1) * (1 + 2 * U2) = radK n C₁ := by
      rw [radK, hU1, hU2]
      ring
    rw [← hKeq]
    set KE : ℝ := ((2*n+1 : ℕ) : ℝ) * (9/8 : ℝ) ^ (2*n) * (1 + 2 * U1)
        + ((2*n+2 : ℕ) : ℝ) * (9/8 : ℝ) ^ (2*n+1) * (1 + 2 * U2) with hKE
    have hR0 : 0 ≤ R := by linarith
    have hr0 : 0 ≤ r := by linarith
    have hRpos : 0 < R := by linarith
    have hrpos : 0 < r := by linarith
    have hc0 : (0 : ℝ) ≤ 9/8 := by norm_num
    have hN1 : (0 : ℝ) ≤ ((2*n+1 : ℕ) : ℝ) := by positivity
    have hN2 : (0 : ℝ) ≤ ((2*n+2 : ℕ) : ℝ) := by positivity
    have hN0 : (0 : ℝ) ≤ ((2*n : ℕ) : ℝ) := by positivity
    have hRpow : R ^ (2*n) ≤ (9/8 : ℝ) ^ (2*n) := pow_le_pow_left₀ hR0 hR2 (2*n)
    have hrpow : r ^ (2*n) ≤ (9/8 : ℝ) ^ (2*n) := pow_le_pow_left₀ hr0 hr2 (2*n)
    have hrpow1 : r ^ (2*n+1) ≤ (9/8 : ℝ) ^ (2*n+1) := pow_le_pow_left₀ hr0 hr2 (2*n+1)
    have hRpowm : R ^ (2*n-1) ≤ (9/8 : ℝ) ^ (2*n-1) := pow_le_pow_left₀ hR0 hR2 (2*n-1)
    have hrpowm : r ^ (2*n-1) ≤ (9/8 : ℝ) ^ (2*n-1) := pow_le_pow_left₀ hr0 hr2 (2*n-1)
    have haε : |a| ≤ ε := le_of_lt ha
    have hbε : |b| ≤ ε := le_of_lt hb
    -- bounds for the four correction terms
    have hX1T : |X1| ≤ U1 * ε := by
      rw [hX1, hU1]
      have heq1 : ((2*n+2 : ℕ) : ℝ) * (((2*n+1 : ℕ) : ℝ) * R ^ (2*n) * R' * R') =
          (((2*n+2 : ℕ) : ℝ) * ((2*n+1 : ℕ) : ℝ)) * (R ^ (2*n) * R' * R') := by ring
      rw [heq1]
      exact abs_coef_mul_le (by positivity) (pow_nonneg hR0 _) hRpow hε0 hε1 hR'
    have hX2T : |X2| ≤ U1 * ε := by
      rw [hX2, hU1]
      have heq2 : ((2*n+2 : ℕ) : ℝ) * (((2*n+1 : ℕ) : ℝ) * r ^ (2*n) * r' * r') =
          (((2*n+2 : ℕ) : ℝ) * ((2*n+1 : ℕ) : ℝ)) * (r ^ (2*n) * r' * r') := by ring
      rw [heq2]
      exact abs_coef_mul_le (by positivity) (pow_nonneg hr0 _) hrpow hε0 hε1 hr'
    have hY1T : |Y1| ≤ U2 * ε := by
      rw [hY1, hU2]
      have heq1 : ((2*n+1 : ℕ) : ℝ) * (((2*n : ℕ) : ℝ) * R ^ (2*n-1) * R' * R') =
          (((2*n+1 : ℕ) : ℝ) * ((2*n : ℕ) : ℝ)) * (R ^ (2*n-1) * R' * R') := by ring
      rw [heq1]
      exact abs_coef_mul_le (by positivity) (pow_nonneg hR0 _) hRpowm hε0 hε1 hR'
    have hY2T : |Y2| ≤ U2 * ε := by
      rw [hY2, hU2]
      have heq2 : ((2*n+1 : ℕ) : ℝ) * (((2*n : ℕ) : ℝ) * r ^ (2*n-1) * r' * r') =
          (((2*n+1 : ℕ) : ℝ) * ((2*n : ℕ) : ℝ)) * (r ^ (2*n-1) * r' * r') := by ring
      rw [heq2]
      exact abs_coef_mul_le (by positivity) (pow_nonneg hr0 _) hrpowm hε0 hε1 hr'
    -- bounds for the two brackets
    have hbr1 : |a - (X1 + X2)| ≤ (1 + 2 * U1) * ε := by
      have h1 : |a - (X1 + X2)| ≤ |a| + |X1| + |X2| := by
        have hsub : |a - (X1 + X2)| ≤ |a| + |X1 + X2| := by
          have h := abs_add_le a (-(X1 + X2))
          rw [abs_neg] at h
          simpa only [sub_eq_add_neg] using h
        have hadd : |X1 + X2| ≤ |X1| + |X2| := abs_add_le X1 X2
        linarith only [hsub, hadd]
      nlinarith [h1, hX1T, hX2T, haε, abs_nonneg a]
    have hbr2 : |b - (Y1 - Y2)| ≤ (1 + 2 * U2) * ε := by
      have h1 : |b - (Y1 - Y2)| ≤ |b| + |Y1| + |Y2| := by
        have hsub : |b - (Y1 - Y2)| ≤ |b| + |Y1 - Y2| := by
          have h := abs_add_le b (-(Y1 - Y2))
          rw [abs_neg] at h
          simpa only [sub_eq_add_neg] using h
        have hadd : |Y1 - Y2| ≤ |Y1| + |Y2| := by
          have h := abs_add_le Y1 (-Y2)
          rw [abs_neg] at h
          simpa only [sub_eq_add_neg] using h
        linarith only [hsub, hadd]
      nlinarith [h1, hY1T, hY2T, hbε, abs_nonneg b]
    -- the two products
    have hcoef1 : ((2*n+1 : ℕ) : ℝ) * r ^ (2*n) ≤ ((2*n+1 : ℕ) : ℝ) * (9/8 : ℝ) ^ (2*n) :=
      mul_le_mul_of_nonneg_left hrpow hN1
    have hcoef2 : ((2*n+2 : ℕ) : ℝ) * r ^ (2*n+1) ≤ ((2*n+2 : ℕ) : ℝ) * (9/8 : ℝ) ^ (2*n+1) :=
      mul_le_mul_of_nonneg_left hrpow1 hN2
    have hterm1 : |((2*n+1 : ℕ) : ℝ) * r ^ (2*n) * (a - (X1 + X2))| ≤
        (((2*n+1 : ℕ) : ℝ) * (9/8 : ℝ) ^ (2*n) * (1 + 2 * U1)) * ε := by
      have e1 : |((2*n+1 : ℕ) : ℝ) * r ^ (2*n) * (a - (X1 + X2))| =
          (((2*n+1 : ℕ) : ℝ) * r ^ (2*n)) * |a - (X1 + X2)| := by
        rw [abs_mul, abs_of_nonneg (mul_nonneg hN1 (pow_nonneg hr0 _))]
      rw [e1]
      calc (((2*n+1 : ℕ) : ℝ) * r ^ (2*n)) * |a - (X1 + X2)|
          ≤ (((2*n+1 : ℕ) : ℝ) * (9/8 : ℝ) ^ (2*n)) * ((1 + 2 * U1) * ε) :=
            mul_le_mul hcoef1 hbr1 (abs_nonneg _) (by positivity)
        _ = (((2*n+1 : ℕ) : ℝ) * (9/8 : ℝ) ^ (2*n) * (1 + 2 * U1)) * ε := by ring
    have hterm2 : |((2*n+2 : ℕ) : ℝ) * r ^ (2*n+1) * (b - (Y1 - Y2))| ≤
        (((2*n+2 : ℕ) : ℝ) * (9/8 : ℝ) ^ (2*n+1) * (1 + 2 * U2)) * ε := by
      have e2 : |((2*n+2 : ℕ) : ℝ) * r ^ (2*n+1) * (b - (Y1 - Y2))| =
          (((2*n+2 : ℕ) : ℝ) * r ^ (2*n+1)) * |b - (Y1 - Y2)| := by
        rw [abs_mul, abs_of_nonneg (mul_nonneg hN2 (pow_nonneg hr0 _))]
      rw [e2]
      calc (((2*n+2 : ℕ) : ℝ) * r ^ (2*n+1)) * |b - (Y1 - Y2)|
          ≤ (((2*n+2 : ℕ) : ℝ) * (9/8 : ℝ) ^ (2*n+1)) * ((1 + 2 * U2) * ε) :=
            mul_le_mul hcoef2 hbr2 (abs_nonneg _) (by positivity)
        _ = (((2*n+2 : ℕ) : ℝ) * (9/8 : ℝ) ^ (2*n+1) * (1 + 2 * U2)) * ε := by ring
    -- assemble
    have hRHS : |((2*n+1 : ℕ) : ℝ) * r ^ (2*n) * (a - (X1 + X2))
        + ((2*n+2 : ℕ) : ℝ) * r ^ (2*n+1) * (b - (Y1 - Y2))| ≤ KE * ε := by
      have hsum : |((2*n+1 : ℕ) : ℝ) * r ^ (2*n) * (a - (X1 + X2))
          + ((2*n+2 : ℕ) : ℝ) * r ^ (2*n+1) * (b - (Y1 - Y2))| ≤
          (((2*n+1 : ℕ) : ℝ) * (9/8 : ℝ) ^ (2*n) * (1 + 2 * U1)) * ε
            + (((2*n+2 : ℕ) : ℝ) * (9/8 : ℝ) ^ (2*n+1) * (1 + 2 * U2)) * ε := by
        have h := abs_add_le (((2*n+1 : ℕ) : ℝ) * r ^ (2*n) * (a - (X1 + X2)))
          (((2*n+2 : ℕ) : ℝ) * r ^ (2*n+1) * (b - (Y1 - Y2)))
        linarith [h, hterm1, hterm2]
      rwa [show (((2*n+1 : ℕ) : ℝ) * (9/8 : ℝ) ^ (2*n) * (1 + 2 * U1)) * ε
            + (((2*n+2 : ℕ) : ℝ) * (9/8 : ℝ) ^ (2*n+1) * (1 + 2 * U2)) * ε = KE * ε from by
          rw [hKE]; ring] at hsum
    -- the coefficient is positive and dominates radD
    have hDpos : 0 < D := by
      rw [hD]
      exact mul_pos (by positivity)
        (add_pos (mul_pos (pow_pos hRpos _) (pow_pos hrpos _))
          (mul_pos (pow_pos hRpos _) (pow_pos hrpos _)))
    have hD0 : radD n ≤ D := radD_le n hR1 hr1
    have hKEpos : 0 ≤ (KE + 1) / radD n := by
      apply div_nonneg
      · rw [hKE, hU1, hU2]; positivity
      · exact le_of_lt (radD_pos n)
    have hC2D : KE ≤ ((KE + 1) / radD n) * D := by
      have h1 : ((KE + 1) / radD n) * radD n = KE + 1 :=
        div_mul_cancel₀ (KE + 1) (ne_of_gt (radD_pos n))
      have h2 : ((KE + 1) / radD n) * radD n ≤ ((KE + 1) / radD n) * D :=
        mul_le_mul_of_nonneg_left hD0 hKEpos
      linarith
    have habs : |R''| * D = |((2*n+1 : ℕ) : ℝ) * r ^ (2*n) * (a - (X1 + X2))
        + ((2*n+2 : ℕ) : ℝ) * r ^ (2*n+1) * (b - (Y1 - Y2))| := by
      have h2 : R'' * D = ((2*n+1 : ℕ) : ℝ) * r ^ (2*n) * (a - (X1 + X2))
          + ((2*n+2 : ℕ) : ℝ) * r ^ (2*n+1) * (b - (Y1 - Y2)) :=
        (mul_comm R'' D).trans heq
      calc |R''| * D = |R'' * D| := by rw [abs_mul, abs_of_pos hDpos]
        _ = |((2*n+1 : ℕ) : ℝ) * r ^ (2*n) * (a - (X1 + X2))
            + ((2*n+2 : ℕ) : ℝ) * r ^ (2*n+1) * (b - (Y1 - Y2))| := by rw [h2]
    have hkey : |R''| * D ≤ (((KE + 1) / radD n) * ε) * D := by
      have hA : |R''| * D ≤ KE * ε := by rw [habs]; exact hRHS
      have hB : KE * ε ≤ ((KE + 1) / radD n) * D * ε :=
        mul_le_mul_of_nonneg_right hC2D hε0
      calc |R''| * D ≤ KE * ε := hA
        _ ≤ ((KE + 1) / radD n) * D * ε := hB
        _ = (((KE + 1) / radD n) * ε) * D := by ring
    exact le_of_mul_le_mul_right hkey hDpos

end Work.OddRadon
