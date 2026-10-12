import Mathlib.Algebra.Order.Star.Real
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseB1Cube

/-- Auxiliary: `√x ≤ 1 + x` for `x ≥ 0`. -/
private lemma sqrt_le_one_add {x : ℝ} (hx : 0 ≤ x) : Real.sqrt x ≤ 1 + x := by
  rw [Real.sqrt_le_left (by linarith)]
  nlinarith [hx, sq_nonneg x]

theorem scB1Case2CoreB1 {c1 Cw Ξ Cman A Kg χ μ V S Q W 𝔉 τf fib Λ : ℝ}
    (hA : 0 < A) (hμ : 0 < μ) (hV : 0 < V) (hΞ : 1 ≤ Ξ) (hCw : 0 ≤ Cw) (hCman : 0 ≤ Cman)
    (hc1 : 0 < c1) (hW0 : 0 ≤ W) (hWle : W ≤ Cw * A * χ) (hS : 0 ≤ S) (hQ : 0 ≤ Q)
    (hχ : 0 ≤ χ) (hτf0 : 0 ≤ τf)
    (hA1 : χ * S ≤ 432 ^ 2 * Ξ * V * Q) (hA2 : χ * μ ≤ 432 ^ 2 * Ξ * Q)
    (hA3 : χ * Λ ≤ 864 * Ξ * Q)
    (hτ : τf ≤ S / V + Λ + Ξ * Q / χ) (hF : 𝔉 ≤ μ * τf + μ ^ 2)
    (hfib : fib ≤ (W / V) * S + Cman * A * (Real.sqrt (Q * (W / V * S)) + Q))
    (hK1 : c1 * Cw * Ξ * (2 * 432 ^ 2 + 864 + 1) ≤ Kg / 4)
    (hK2 : Cw * 432 ^ 2 * Ξ ≤ Kg / 4)
    (hK3 : 432 * Cman * (1 + Cw * Ξ) * (1 + A) ≤ Kg / 4)
    (hK4 : Cman ≤ Kg / 4) :
    c1 * (W * 𝔉) + μ * fib ≤ Kg * μ * A * Q := by
  have hA0 : 0 ≤ A := hA.le
  have hμ0 : 0 ≤ μ := hμ.le
  have hΞ0 : 0 ≤ Ξ := by linarith
  have hc10 : 0 ≤ c1 := hc1.le
  have hAMQ : 0 ≤ A * μ * Q := mul_nonneg (mul_nonneg hA0 hμ0) hQ
  -- `χ · τf` controlled by the three absorption hypotheses
  have hχτ : χ * τf ≤ χ * S / V + χ * Λ + Ξ * Q := by
    have h := mul_le_mul_of_nonneg_left hτ hχ
    have hexp : χ * (S / V + Λ + Ξ * Q / χ)
        = χ * S / V + χ * Λ + χ * (Ξ * Q / χ) := by ring
    rw [hexp] at h
    have hdiv : χ * (Ξ * Q / χ) ≤ Ξ * Q := by
      rcases eq_or_lt_of_le hχ with h0 | hlt
      · rw [← h0]; simp only [zero_mul]; exact mul_nonneg hΞ0 hQ
      · have : χ * (Ξ * Q / χ) = Ξ * Q := by field_simp
        exact le_of_eq this
    linarith [h, hdiv]
  have hτS : χ * S / V ≤ 432 ^ 2 * Ξ * Q := by
    rw [div_le_iff₀ hV]; nlinarith [hA1]
  -- (A) the first term `c1 * (W * 𝔉)`
  have hterm1 : c1 * (W * 𝔉) ≤ Kg / 4 * (A * μ * Q) := by
    have hμτ : 0 ≤ μ * τf + μ ^ 2 := by
      nlinarith [mul_nonneg hμ0 hτf0, sq_nonneg μ]
    have hstepW : W * 𝔉 ≤ (Cw * A * χ) * (μ * τf + μ ^ 2) := by
      calc W * 𝔉 ≤ W * (μ * τf + μ ^ 2) := mul_le_mul_of_nonneg_left hF hW0
        _ ≤ (Cw * A * χ) * (μ * τf + μ ^ 2) := mul_le_mul_of_nonneg_right hWle hμτ
    have h1 : c1 * (W * 𝔉) ≤ c1 * ((Cw * A * χ) * (μ * τf + μ ^ 2)) :=
      mul_le_mul_of_nonneg_left hstepW hc10
    have h2 : c1 * ((Cw * A * χ) * (μ * τf + μ ^ 2))
        ≤ c1 * Cw * Ξ * (2 * 432 ^ 2 + 864 + 1) * (A * μ * Q) := by
      have hexp : (Cw * A * χ) * (μ * τf + μ ^ 2)
          = Cw * A * μ * (χ * τf) + Cw * A * μ * (χ * μ) := by ring
      rw [hexp]
      have hbound : χ * τf + χ * μ
          ≤ 432 ^ 2 * Ξ * Q + 864 * Ξ * Q + Ξ * Q + 432 ^ 2 * Ξ * Q := by
        linarith [hχτ, hτS, hA3, hA2]
      have hsum : Cw * A * μ * (χ * τf) + Cw * A * μ * (χ * μ)
          = Cw * A * μ * (χ * τf + χ * μ) := by ring
      rw [hsum]
      have hb := mul_le_mul_of_nonneg_left hbound (by positivity : (0:ℝ) ≤ Cw * A * μ)
      have hrhs : Cw * A * μ * (432 ^ 2 * Ξ * Q + 864 * Ξ * Q + Ξ * Q + 432 ^ 2 * Ξ * Q)
          = Cw * Ξ * (2 * 432 ^ 2 + 864 + 1) * (A * μ * Q) := by ring
      rw [hrhs] at hb
      calc c1 * (Cw * A * μ * (χ * τf + χ * μ))
          ≤ c1 * (Cw * Ξ * (2 * 432 ^ 2 + 864 + 1) * (A * μ * Q)) :=
            mul_le_mul_of_nonneg_left hb hc10
        _ = c1 * Cw * Ξ * (2 * 432 ^ 2 + 864 + 1) * (A * μ * Q) := by ring
    have hK1' := mul_le_mul_of_nonneg_right hK1 hAMQ
    linarith [h1, h2, hK1']
  -- the square-root estimate
  have hsqrtB : Real.sqrt (Q * (W / V * S)) ≤ 432 * Real.sqrt (Cw * A * Ξ) * Q := by
    have hWdiv : W / V ≤ Cw * A * χ / V := by
      rw [div_le_div_iff_of_pos_right hV]; exact hWle
    have h1 : W / V * S ≤ 432 ^ 2 * (Cw * A * Ξ) * Q := by
      have h2 : W / V * S ≤ (Cw * A * χ / V) * S := mul_le_mul_of_nonneg_right hWdiv hS
      have h3 : (Cw * A * χ / V) * S = Cw * A * (χ * S / V) := by ring
      rw [h3] at h2
      have h4 : Cw * A * (χ * S / V) ≤ Cw * A * (432 ^ 2 * Ξ * Q) :=
        mul_le_mul_of_nonneg_left hτS (by positivity)
      linarith [h2, h4]
    rw [Real.sqrt_le_left (by positivity : (0:ℝ) ≤ 432 * Real.sqrt (Cw * A * Ξ) * Q)]
    have hs : (432 * Real.sqrt (Cw * A * Ξ) * Q) ^ 2 = 432 ^ 2 * (Cw * A * Ξ) * Q ^ 2 := by
      rw [mul_pow, mul_pow, Real.sq_sqrt (by positivity)]
    rw [hs]
    nlinarith [h1, hQ]
  -- the constant gate for the square-root term
  have hcoef : 432 * Cman * Real.sqrt (Cw * A * Ξ) ≤ Kg / 4 := by
    have hs1 : Real.sqrt (Cw * A * Ξ) ≤ 1 + Cw * A * Ξ :=
      sqrt_le_one_add (by positivity)
    have hs2 : 1 + Cw * A * Ξ ≤ (1 + Cw * Ξ) * (1 + A) := by
      nlinarith [mul_nonneg hCw hΞ0, mul_nonneg hCw (mul_nonneg hΞ0 hA0),
        mul_nonneg hA0 hΞ0, mul_nonneg hCw hA0]
    have h3 : 432 * Cman * Real.sqrt (Cw * A * Ξ) ≤ 432 * Cman * (1 + Cw * Ξ) * (1 + A) := by
      have h4 : 432 * Cman * Real.sqrt (Cw * A * Ξ)
          ≤ 432 * Cman * ((1 + Cw * Ξ) * (1 + A)) :=
        mul_le_mul_of_nonneg_left (le_trans hs1 hs2) (by positivity)
      have he : 432 * Cman * ((1 + Cw * Ξ) * (1 + A))
          = 432 * Cman * (1 + Cw * Ξ) * (1 + A) := by ring
      linarith [h4, le_of_eq he]
    linarith [h3, hK3]
  -- (B1) the `(W/V)·S` row
  have hB1 : μ * ((W / V) * S) ≤ Kg / 4 * (A * μ * Q) := by
    have hWdiv : W / V ≤ Cw * A * χ / V := by
      rw [div_le_div_iff_of_pos_right hV]; exact hWle
    have h1 : (W / V) * S ≤ Cw * A * (χ * S / V) := by
      have h := mul_le_mul_of_nonneg_right hWdiv hS
      have he : Cw * A * χ / V * S = Cw * A * (χ * S / V) := by ring
      rw [he] at h
      exact h
    have h2 : Cw * A * (χ * S / V) ≤ Cw * A * (432 ^ 2 * Ξ * Q) :=
      mul_le_mul_of_nonneg_left hτS (by positivity)
    have h3 : W / V * S ≤ Cw * A * 432 ^ 2 * Ξ * Q := by linarith [h1, h2]
    have h4 : μ * (W / V * S) ≤ (Cw * 432 ^ 2 * Ξ) * (A * μ * Q) := by
      have h := mul_le_mul_of_nonneg_left h3 hμ0
      have he : μ * (Cw * A * 432 ^ 2 * Ξ * Q) = (Cw * 432 ^ 2 * Ξ) * (A * μ * Q) := by ring
      linarith [h, le_of_eq he]
    have hK := mul_le_mul_of_nonneg_right hK2 hAMQ
    linarith [h4, hK]
  -- (B2) the square-root row
  have hB2 : μ * (Cman * A * Real.sqrt (Q * (W / V * S))) ≤ Kg / 4 * (A * μ * Q) := by
    have hb : μ * (Cman * A * Real.sqrt (Q * (W / V * S)))
        ≤ μ * (Cman * A * (432 * Real.sqrt (Cw * A * Ξ) * Q)) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hsqrtB (by positivity)) hμ0
    have he : μ * (Cman * A * (432 * Real.sqrt (Cw * A * Ξ) * Q))
        = (432 * Cman * Real.sqrt (Cw * A * Ξ)) * (A * μ * Q) := by ring
    rw [he] at hb
    have hK := mul_le_mul_of_nonneg_right hcoef hAMQ
    linarith [hb, hK]
  -- (B3) the `Q` row
  have hB3 : μ * (Cman * A * Q) ≤ Kg / 4 * (A * μ * Q) := by
    have hK := mul_le_mul_of_nonneg_right hK4 hAMQ
    have he : μ * (Cman * A * Q) = Cman * (A * μ * Q) := by ring
    linarith [hK, le_of_eq he]
  -- assemble the second term
  have hfib' : μ * fib ≤ μ * ((W / V) * S + Cman * A * (Real.sqrt (Q * (W / V * S)) + Q)) :=
    mul_le_mul_of_nonneg_left hfib hμ0
  have hexp : μ * ((W / V) * S + Cman * A * (Real.sqrt (Q * (W / V * S)) + Q))
      = μ * ((W / V) * S) + μ * (Cman * A * Real.sqrt (Q * (W / V * S))) + μ * (Cman * A * Q) := by
    ring
  rw [hexp] at hfib'
  linarith [hterm1, hfib', hB1, hB2, hB3]

end Work.BoseB1Cube
