import Mathlib
import Submission.Work.ZeroFreeTables.OffAxis.G72Base

namespace Work.ZeroFreeTables.OffAxis

/-- The real numerator of `RB72` as a polynomial in `(s,σ)`. -/
private def NB72 (s σ : ℝ) : ℝ :=
  ((1-s)^2 - σ^2)*(s^6 - 15*s^4*σ^2 + 15*s^2*σ^4 - σ^6)
    - (2*(1-s)*σ)*(6*s^5*σ - 20*s^3*σ^3 + 6*s*σ^5)

/-- The real numerator of `RI72` as a polynomial in `(s,σ)`. -/
private def NI72 (s σ : ℝ) : ℝ :=
  ((1-s)^2 - σ^2)*(6*s^5*σ - 20*s^3*σ^3 + 6*s*σ^5)
    + (2*(1-s)*σ)*(s^6 - 15*s^4*σ^2 + 15*s^2*σ^4 - σ^6)

private lemma RB72_eq (s σ : ℝ) : RB72 s σ = 4*NB72 s σ/(s^2+σ^2)^6 := by
  rw [RB72, NB72]

private lemma RI72_eq (s σ : ℝ) : RI72 s σ = 4*NI72 s σ/(s^2+σ^2)^6 := by
  rw [RI72, NI72]

/-- `NB72 + i·NI72 = ((1-s)+iσ)^2 (s+iσ)^6`, so the squares sum to the squared modulus. -/
private lemma NB72_sq_add_NI72_sq (s σ : ℝ) :
    NB72 s σ ^ 2 + NI72 s σ ^ 2 = ((1-s)^2+σ^2)^2 * (s^2+σ^2)^6 := by
  rw [NB72, NI72]; ring

/-- The key pointwise bound: `|cos 2σ · NB72 + sin 2σ · NI72| ≤ ((1-s)² + σ²)(s²+σ²)³`. -/
private lemma trig_comb_bound (s σ : ℝ) :
    |Real.cos (2*σ) * NB72 s σ + Real.sin (2*σ) * NI72 s σ|
      ≤ ((1-s)^2+σ^2) * (s^2+σ^2)^3 := by
  have hcs := Real.cos_sq_add_sin_sq (2*σ)
  have hMsq := NB72_sq_add_NI72_sq s σ
  have hX : (Real.cos (2*σ) * NB72 s σ + Real.sin (2*σ) * NI72 s σ)^2
      ≤ ((1-s)^2+σ^2)^2 * (s^2+σ^2)^6 := by
    nlinarith [sq_nonneg (Real.sin (2*σ)*NB72 s σ - Real.cos (2*σ)*NI72 s σ), hMsq, hcs]
  have hnn : 0 ≤ ((1-s)^2+σ^2) * (s^2+σ^2)^3 := by positivity
  have h2 : (Real.cos (2*σ) * NB72 s σ + Real.sin (2*σ) * NI72 s σ)^2
      ≤ (((1-s)^2+σ^2) * (s^2+σ^2)^3)^2 := by
    calc (Real.cos (2*σ) * NB72 s σ + Real.sin (2*σ) * NI72 s σ)^2
        ≤ ((1-s)^2+σ^2)^2 * (s^2+σ^2)^6 := hX
      _ = (((1-s)^2+σ^2) * (s^2+σ^2)^3)^2 := by ring
  simpa [abs_of_nonneg hnn] using (sq_le_sq.mp h2)

theorem G72TrigBound (s σ : ℝ) :
    |Real.cos (2*σ) * Work.ZeroFreeTables.OffAxis.RB72 s σ
      + Real.sin (2*σ) * Work.ZeroFreeTables.OffAxis.RI72 s σ|
      ≤ 4 * ((1-s)^2 + σ^2) / (s^2 + σ^2)^3 := by
  by_cases hD0 : s^2 + σ^2 = 0
  · have hs2 : s^2 = 0 := by nlinarith [sq_nonneg s, sq_nonneg σ]
    have hσ2 : σ^2 = 0 := by nlinarith [sq_nonneg s, sq_nonneg σ]
    have hs : s = 0 := sq_eq_zero_iff.mp hs2
    have hσ : σ = 0 := sq_eq_zero_iff.mp hσ2
    subst hs; subst hσ
    norm_num [RB72, RI72]
  · have hDpos : 0 < s^2 + σ^2 := lt_of_le_of_ne (by positivity) (Ne.symm hD0)
    have hE : Real.cos (2*σ) * RB72 s σ + Real.sin (2*σ) * RI72 s σ
        = 4 * (Real.cos (2*σ) * NB72 s σ + Real.sin (2*σ) * NI72 s σ) / (s^2+σ^2)^6 := by
      rw [RB72_eq, RI72_eq]; ring_nf
    rw [hE]
    have hD6 : (0:ℝ) < (s^2+σ^2)^6 := pow_pos hDpos 6
    have hD3 : (0:ℝ) < (s^2+σ^2)^3 := pow_pos hDpos 3
    rw [abs_div, abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 4), abs_of_pos hD6]
    rw [div_le_div_iff₀ hD6 hD3]
    have key : 4*|Real.cos (2*σ) * NB72 s σ + Real.sin (2*σ) * NI72 s σ| * (s^2+σ^2)^3
        ≤ 4*((1-s)^2+σ^2) * (s^2+σ^2)^6 := by
      calc 4*|Real.cos (2*σ) * NB72 s σ + Real.sin (2*σ) * NI72 s σ| * (s^2+σ^2)^3
          ≤ (4*(((1-s)^2+σ^2)*(s^2+σ^2)^3)) * (s^2+σ^2)^3 := by
              apply mul_le_mul_of_nonneg_right _ (by positivity)
              linarith [trig_comb_bound s σ]
        _ = 4*((1-s)^2+σ^2) * (s^2+σ^2)^6 := by ring
    exact key

end Work.ZeroFreeTables.OffAxis
