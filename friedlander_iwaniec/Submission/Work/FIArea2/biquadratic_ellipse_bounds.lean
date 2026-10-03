import Mathlib

namespace Work.FIArea2

open scoped BigOperators

/-- The geometry of the biquadratic ellipse `g(t₁,t₂) = t₁⁴ - 2γt₁²t₂² + t₂⁴` of FI §7, (7.2)–(7.4):
for `0 ≤ γ < 1` and `M > 0`, the level region `M/4 < g < 4M` is squeezed between the two
"squares annuli" of (7.3).  These are the estimates behind the bound `O(M^{1/2} log δ^{-2})` for
the area of integration (7.4) and are used in the integration-by-parts of Lemma 7.1.

Route: put `A = t₁²`, `B = t₂² ≥ 0`; then `g = (A-B)² + 2(1-γ)AB`, and the first three conjuncts are
`(1+γ²)(A²+B²) - 4γAB ≥ 0` (AM–GM), `2(1-γ)AB ≥ 0`, `2(1+γ)AB ≥ 0`.  For the last conjunct use
`(A-B)² ≤ g < 4M`, `(A+B)² ≥ g > M/4`, `(1-γ²)(A²+B²) ≤ 2g < 8M` and `(A+B)² ≤ 2(A²+B²)`. -/
theorem biquadratic_ellipse_bounds (γ M t₁ t₂ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (hM : 0 < M) :
    ((1 - γ ^ 2) * (t₁ ^ 4 + t₂ ^ 4) ≤ 2 * (t₁ ^ 4 - 2 * γ * t₁ ^ 2 * t₂ ^ 2 + t₂ ^ 4) ∧
     (t₁ ^ 2 - t₂ ^ 2) ^ 2 ≤ t₁ ^ 4 - 2 * γ * t₁ ^ 2 * t₂ ^ 2 + t₂ ^ 4 ∧
     t₁ ^ 4 - 2 * γ * t₁ ^ 2 * t₂ ^ 2 + t₂ ^ 4 ≤ (t₁ ^ 2 + t₂ ^ 2) ^ 2) ∧
    (M / 4 < t₁ ^ 4 - 2 * γ * t₁ ^ 2 * t₂ ^ 2 + t₂ ^ 4 →
     t₁ ^ 4 - 2 * γ * t₁ ^ 2 * t₂ ^ 2 + t₂ ^ 4 < 4 * M →
     |t₁ ^ 2 - t₂ ^ 2| < 2 * Real.sqrt M ∧
     Real.sqrt M / 2 < t₁ ^ 2 + t₂ ^ 2 ∧
     t₁ ^ 2 + t₂ ^ 2 < 4 * Real.sqrt M / Real.sqrt (1 - γ ^ 2)) := by
  -- Conjunct 1: `2g - (1-γ²)(t₁⁴+t₂⁴) = (1-γ)²(t₁⁴+t₂⁴) + 2γ(t₁²-t₂²)² ≥ 0`.
  have hc1 : (1 - γ^2) * (t₁^4 + t₂^4) ≤ 2 * (t₁^4 - 2*γ*t₁^2*t₂^2 + t₂^4) := by
    have hid : 2 * (t₁^4 - 2*γ*t₁^2*t₂^2 + t₂^4) - (1-γ^2)*(t₁^4+t₂^4)
        = (1-γ)^2*(t₁^4+t₂^4) + 2*γ*(t₁^2-t₂^2)^2 := by ring
    nlinarith [sq_nonneg (1-γ), sq_nonneg (t₁^2 - t₂^2), sq_nonneg (t₁^2), sq_nonneg (t₂^2), hγ0]
  -- Conjunct 2: `g - (t₁²-t₂²)² = 2(1-γ)t₁²t₂² ≥ 0`.
  have hc2 : (t₁^2 - t₂^2)^2 ≤ t₁^4 - 2*γ*t₁^2*t₂^2 + t₂^4 := by
    have hid : (t₁^4 - 2*γ*t₁^2*t₂^2 + t₂^4) - (t₁^2-t₂^2)^2 = 2*(1-γ)*t₁^2*t₂^2 := by ring
    have h1γ : 0 ≤ 1 - γ := by linarith
    have hnn : 0 ≤ 2 * (1 - γ) * t₁^2 * t₂^2 := by positivity
    nlinarith [hid, hnn]
  -- Conjunct 3: `(t₁²+t₂²)² - g = 2(1+γ)t₁²t₂² ≥ 0`.
  have hc3 : t₁^4 - 2*γ*t₁^2*t₂^2 + t₂^4 ≤ (t₁^2+t₂^2)^2 := by
    have hid : (t₁^2+t₂^2)^2 - (t₁^4 - 2*γ*t₁^2*t₂^2 + t₂^4) = 2*(1+γ)*t₁^2*t₂^2 := by ring
    have h1γ : 0 ≤ 1 + γ := by linarith
    have hnn : 0 ≤ 2 * (1 + γ) * t₁^2 * t₂^2 := by positivity
    nlinarith [hid, hnn]
  refine ⟨⟨hc1, hc2, hc3⟩, ?_⟩
  intro hlow hhigh
  refine ⟨?_, ?_, ?_⟩
  · -- `|t₁² - t₂²| < 2√M`  from `(t₁²-t₂²)² ≤ g < 4M = (2√M)²`.
    have hs : (t₁^2 - t₂^2)^2 < (2*Real.sqrt M)^2 := by
      have he : (2*Real.sqrt M)^2 = 4*M := by rw [mul_pow, Real.sq_sqrt hM.le]; ring
      rw [he]
      linarith [hc2, hhigh]
    have h2Mnn : 0 ≤ 2*Real.sqrt M := by positivity
    have h := sq_lt_sq.mp hs
    rw [abs_of_nonneg h2Mnn] at h
    exact h
  · -- `√M/2 < t₁² + t₂²`  from `(√M/2)² = M/4 < g ≤ (t₁²+t₂²)²`.
    have hs : (Real.sqrt M / 2)^2 < (t₁^2 + t₂^2)^2 := by
      have he : (Real.sqrt M / 2)^2 = M/4 := by rw [div_pow, Real.sq_sqrt hM.le]; norm_num
      rw [he]
      linarith [hc3, hlow]
    have hxnn : 0 ≤ Real.sqrt M / 2 := by positivity
    have hynn : 0 ≤ t₁^2 + t₂^2 := by positivity
    have h := sq_lt_sq.mp hs
    rw [abs_of_nonneg hxnn, abs_of_nonneg hynn] at h
    exact h
  · -- `t₁² + t₂² < 4√M/√(1-γ²)`  from `(t₁²+t₂²)²(1-γ²) ≤ 2(1-γ²)(t₁⁴+t₂⁴) ≤ 4g < 16M`.
    have hpos : 0 < 1 - γ^2 := by
      have h1 : 0 < 1 - γ := by linarith
      have h2' : 0 < 1 + γ := by linarith
      nlinarith [mul_pos h1 h2']
    have hsqrt_pos : 0 < Real.sqrt (1-γ^2) := Real.sqrt_pos.mpr hpos
    have hAB2 : (t₁^2+t₂^2)^2 ≤ 2*(t₁^4+t₂^4) := by nlinarith [sq_nonneg (t₁^2 - t₂^2)]
    have hA2B2 : (1-γ^2)*(t₁^4+t₂^4) < 8*M := by linarith [hc1, hhigh]
    have hmul : (t₁^2+t₂^2)^2 * (1-γ^2) ≤ 2*((1-γ^2)*(t₁^4+t₂^4)) := by
      have := mul_le_mul_of_nonneg_right hAB2 hpos.le
      nlinarith [this]
    have hbig : (t₁^2+t₂^2)^2 * (1-γ^2) < 16*M := by nlinarith [hmul, hA2B2]
    have hs : ((t₁^2+t₂^2)*Real.sqrt (1-γ^2))^2 < (4*Real.sqrt M)^2 := by
      have e1 : ((t₁^2+t₂^2)*Real.sqrt (1-γ^2))^2 = (t₁^2+t₂^2)^2*(1-γ^2) := by
        rw [mul_pow, Real.sq_sqrt hpos.le]
      have e2 : (4*Real.sqrt M)^2 = 16*M := by rw [mul_pow, Real.sq_sqrt hM.le]; ring
      rw [e1, e2]; exact hbig
    have hlnn : 0 ≤ (t₁^2+t₂^2)*Real.sqrt (1-γ^2) := by positivity
    have hrnn : 0 ≤ 4*Real.sqrt M := by positivity
    have h := sq_lt_sq.mp hs
    rw [abs_of_nonneg hlnn, abs_of_nonneg hrnn] at h
    rw [lt_div_iff₀ hsqrt_pos]
    exact h

end Work.FIArea2
