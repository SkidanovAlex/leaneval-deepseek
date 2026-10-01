import Mathlib

set_option maxHeartbeats 1000000

namespace Work.ZeroDensity.Jutila.LzAux

/-- For `y > 0` and any `n`, `exp (-y) ≤ n! / y ^ n`.  Immediate from the Taylor bound
`y ^ n / n ! ≤ exp y`. -/
lemma exp_neg_le_fact_div_pow (n : ℕ) {y : ℝ} (hy : 0 < y) :
    Real.exp (-y) ≤ (n.factorial : ℝ) / y ^ n := by
  have h := Real.pow_div_factorial_le_exp y (le_of_lt hy) n
  have hpos : 0 < y ^ n / (n.factorial : ℝ) := by positivity
  calc Real.exp (-y) = (Real.exp y)⁻¹ := Real.exp_neg y
    _ ≤ (y ^ n / (n.factorial : ℝ))⁻¹ := by
        have h' := one_div_le_one_div_of_le hpos h
        rwa [one_div, one_div] at h'
    _ = (n.factorial : ℝ) / y ^ n := by rw [inv_div]

/-- The explicit decay used to absorb the Mertens errors: for `c > 0` and `1 ≤ b`,
`exp (-(c √b)) ≤ 8! / (c⁸ b⁴)`. -/
lemma exp_sqrt_bound {c b : ℝ} (hc : 0 < c) (hb1 : 1 ≤ b) :
    Real.exp (-(c * Real.sqrt b)) ≤ 40320 / (c^8 * b^4) := by
  have hb0 : 0 < b := lt_of_lt_of_le zero_lt_one hb1
  have hy : 0 < c * Real.sqrt b := by
    have : 0 < Real.sqrt b := Real.sqrt_pos.2 hb0
    positivity
  have h := exp_neg_le_fact_div_pow 8 hy
  have hpow : (c * Real.sqrt b)^8 = c^8 * b^4 := by
    rw [mul_pow]
    congr 1
    rw [show (Real.sqrt b)^8 = ((Real.sqrt b)^2)^4 by ring, Real.sq_sqrt hb0.le]
  rw [hpow] at h
  have hfac_nat : Nat.factorial 8 = 40320 := by norm_num
  have hfac : (Nat.factorial 8 : ℝ) = 40320 := by rw [hfac_nat]; norm_num
  rw [hfac] at h
  exact h

/-- Polynomial growth is absorbed by the fourth power, on the range `b ≥ 1`. -/
lemma log2_poly_large {b : ℝ} (hb : 1 ≤ b) :
    (1 + (Real.log 2 + b))^2 * (1 + (1 + (Real.log 2 + b))^2)
      ≤ ((2 + Real.log 2)^2 * (1 + (2 + Real.log 2)^2)) * b^4 := by
  have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hb2 : 1 ≤ b^2 := by nlinarith [hb, sq_nonneg (b - 1)]
  have hw : 1 + (Real.log 2 + b) ≤ (2 + Real.log 2) * b := by nlinarith [hlog2, hb]
  have hu0 : 0 ≤ 1 + (Real.log 2 + b) := by linarith
  have h1 : (1 + (Real.log 2 + b))^2 ≤ ((2 + Real.log 2)*b)^2 := pow_le_pow_left₀ hu0 hw 2
  have h2 : 1 + (1 + (Real.log 2 + b))^2 ≤ 1 + ((2 + Real.log 2)*b)^2 := by
    have hp := pow_le_pow_left₀ hu0 hw 2; linarith
  have h3 : (1 + (Real.log 2 + b))^2 * (1 + (1 + (Real.log 2 + b))^2)
      ≤ ((2 + Real.log 2)*b)^2 * (1 + ((2 + Real.log 2)*b)^2) :=
    mul_le_mul h1 h2 (by positivity) (by positivity)
  refine le_trans h3 ?_
  calc ((2 + Real.log 2)*b)^2 * (1 + ((2 + Real.log 2)*b)^2)
      = ((2 + Real.log 2)^2 * b^2) * (1 + (2 + Real.log 2)^2 * b^2) := by ring
    _ ≤ ((2 + Real.log 2)^2 * b^2) * ((1 + (2 + Real.log 2)^2) * b^2) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        nlinarith [hb2, hlog2]
    _ = ((2 + Real.log 2)^2 * (1 + (2 + Real.log 2)^2)) * b^4 := by ring

/-- The small-`b` range `0 ≤ b ≤ 1` is bounded outright. -/
lemma log2_poly_small {b : ℝ} (hb0 : 0 ≤ b) (hb1 : b ≤ 1) :
    (1 + (Real.log 2 + b))^2 * (1 + (1 + (Real.log 2 + b))^2)
      ≤ (2 + Real.log 2)^2 * (1 + (2 + Real.log 2)^2) := by
  have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hw : 1 + (Real.log 2 + b) ≤ 2 + Real.log 2 := by linarith
  have hu0 : 0 ≤ 1 + (Real.log 2 + b) := by linarith
  have h1 : (1 + (Real.log 2 + b))^2 ≤ (2 + Real.log 2)^2 := pow_le_pow_left₀ hu0 hw 2
  have h2 : 1 + (1 + (Real.log 2 + b))^2 ≤ 1 + (2 + Real.log 2)^2 := by
    have hp := pow_le_pow_left₀ hu0 hw 2; linarith
  exact mul_le_mul h1 h2 (by positivity) (by positivity)

/-- Decay-versus-logarithm comparison used to absorb the Mertens errors: for `c > 0` there is `K > 0` with
`(1+log Y)²·exp(−c√(log R)) ≤ K/(1+(log Y)²)` whenever `1 ≤ Y ≤ 2R`.
Reason: `exp(−y) ≤ 24/y⁸` (`y⁸/8! ≤ exp y`) gives `exp(−c√(log R)) ≤ 24/(c⁸(log R)⁴)`, while
`Y ≤ 2R` gives `log Y ≤ log 2 + log R`, so `(1+log Y)²(1+(log Y)²) ≤ C(1+log R)²(1+(log R)²)` and
`(1+x)²(1+x²)/x⁴` is bounded for `x ≥ 1`; the range `log R ≤ 1` is bounded separately. -/
theorem ExpSqrtLogMulLogSq {c : ℝ} (hc : 0 < c) :
    ∃ K : ℝ, 0 < K ∧ ∀ Y R : ℝ, 1 ≤ Y → 1 ≤ R → Y ≤ 2 * R →
      (1 + Real.log Y)^2 * Real.exp (-(c * Real.sqrt (Real.log R)))
        ≤ K / (1 + (Real.log Y)^2) := by
  refine ⟨(2 + Real.log 2)^2 * (1 + (2 + Real.log 2)^2)
      + 40320 * ((2 + Real.log 2)^2 * (1 + (2 + Real.log 2)^2)) / c^8 + 1, ?_, ?_⟩
  · have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hA : 0 < (2 + Real.log 2)^2 * (1 + (2 + Real.log 2)^2) := by positivity
    have hB : 0 ≤ 40320 * ((2 + Real.log 2)^2 * (1 + (2 + Real.log 2)^2)) / c^8 := by positivity
    linarith
  · intro Y R hY hR hYR
    set C : ℝ := (2 + Real.log 2)^2 * (1 + (2 + Real.log 2)^2) with hCdef
    have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hCpos : 0 < C := by rw [hCdef]; positivity
    set a := Real.log Y with ha
    set b := Real.log R with hb
    have ha0 : 0 ≤ a := by rw [ha]; exact Real.log_nonneg hY
    have hb0 : 0 ≤ b := by rw [hb]; exact Real.log_nonneg hR
    have hab : a ≤ Real.log 2 + b := by
      rw [ha, hb]
      have hY0 : 0 < Y := lt_of_lt_of_le zero_lt_one hY
      have hR0 : 0 < R := lt_of_lt_of_le zero_lt_one hR
      have h1 := Real.log_le_log hY0 hYR
      rwa [Real.log_mul (by norm_num) (ne_of_gt hR0)] at h1
    have hEYle : (1 + a)^2 * (1 + a^2)
        ≤ (1 + (Real.log 2 + b))^2 * (1 + (1 + (Real.log 2 + b))^2) := by
      have h1a : (1 + a)^2 ≤ (1 + (Real.log 2 + b))^2 :=
        pow_le_pow_left₀ (by linarith) (by linarith) 2
      have ha2 : a^2 ≤ (1 + (Real.log 2 + b))^2 :=
        pow_le_pow_left₀ ha0 (by linarith) 2
      exact mul_le_mul h1a (by linarith) (by positivity) (by positivity)
    have hPE : (1 + a)^2 * (1 + a^2) * Real.exp (-(c * Real.sqrt b))
        ≤ (1 + (Real.log 2 + b))^2 * (1 + (1 + (Real.log 2 + b))^2)
            * Real.exp (-(c * Real.sqrt b)) :=
      mul_le_mul_of_nonneg_right hEYle (Real.exp_pos _).le
    have hK1 : 40320 * C / c^8 ≤ C + 40320 * C / c^8 + 1 := by
      have : 0 ≤ C + 1 := by linarith
      linarith
    have hK2 : C ≤ C + 40320 * C / c^8 + 1 := by
      have h1 : 0 ≤ 40320 * C / c^8 := by positivity
      linarith
    have hmain : (1 + a)^2 * (1 + a^2) * Real.exp (-(c * Real.sqrt b))
        ≤ C + 40320 * C / c^8 + 1 := by
      by_cases hb1 : 1 ≤ b
      · have hp := log2_poly_large hb1
        have hE := exp_sqrt_bound hc hb1
        have hstep : (1 + (Real.log 2 + b))^2 * (1 + (1 + (Real.log 2 + b))^2)
              * Real.exp (-(c * Real.sqrt b)) ≤ 40320 * C / c^8 := by
          have hle := mul_le_mul hp hE (Real.exp_pos _).le
            (mul_nonneg hCpos.le (by positivity : (0:ℝ) ≤ b^4))
          have hEq : ((2 + Real.log 2)^2 * (1 + (2 + Real.log 2)^2) * b^4)
                * (40320 / (c^8 * b^4)) = 40320 * C / c^8 := by
            rw [hCdef]
            have hb4 : b^4 ≠ 0 := by positivity
            have hc8 : c^8 ≠ 0 := by positivity
            have hd : c^8 * b^4 ≠ 0 := by positivity
            field_simp
          rw [hEq] at hle
          exact hle
        exact le_trans (le_trans hPE hstep) hK1
      · have hb1' : b ≤ 1 := le_of_lt (not_le.mp hb1)
        have hp := log2_poly_small hb0 hb1'
        have hE1 : Real.exp (-(c * Real.sqrt b)) ≤ 1 := by
          rw [Real.exp_le_one_iff]
          have : 0 ≤ c * Real.sqrt b := mul_nonneg hc.le (Real.sqrt_nonneg b)
          linarith
        have hstep : (1 + (Real.log 2 + b))^2 * (1 + (1 + (Real.log 2 + b))^2)
              * Real.exp (-(c * Real.sqrt b)) ≤ C := by
          have hle := mul_le_mul hp hE1 (Real.exp_pos _).le
            (by positivity : (0:ℝ) ≤ (2 + Real.log 2)^2 * (1 + (2 + Real.log 2)^2))
          simpa [hCdef, mul_one] using hle
        exact le_trans (le_trans hPE hstep) hK2
    have hdiv : (1 + a)^2 * Real.exp (-(c * Real.sqrt b))
        = ((1 + a)^2 * (1 + a^2) * Real.exp (-(c * Real.sqrt b))) / (1 + a^2) := by
      rw [show (1 + a)^2 * (1 + a^2) * Real.exp (-(c * Real.sqrt b))
            = ((1 + a)^2 * Real.exp (-(c * Real.sqrt b))) * (1 + a^2) by ring]
      exact (mul_div_cancel_right₀ _ (by positivity : (1:ℝ) + a^2 ≠ 0)).symm
    rw [hdiv]
    exact div_le_div_of_nonneg_right hmain (by positivity)

end Work.ZeroDensity.Jutila.LzAux
