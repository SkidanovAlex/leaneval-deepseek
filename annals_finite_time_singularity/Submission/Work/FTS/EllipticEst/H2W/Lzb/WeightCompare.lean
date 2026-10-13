import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.H2W.Lzb

/-- Pointwise lower bounds for the angular weight `sin s cos²s` on the two halves of `(0, π/2)`,
used to compare an arbitrary `L¹`-weighted source with the weight at the point `θ`:
* on `[θ, π/4]` (so `0 < θ ≤ s ≤ π/4`) the weight is at least `θ/π`;
* on `[π/4, θ]` (so `π/4 ≤ s ≤ θ < π/2`) the weight is at least `(2√2/π²)(π/2-θ)²`.
Both follow from `Real.mul_le_sin` (Jordan), `Real.sin_le`/`Real.cos_le` monotonicity on `[0,π/2]`
and `cos(π/4) = √2/2`, `sin(π/4) = √2/2`. -/
theorem WeightCompare :
    (∀ θ s : ℝ, 0 < θ → θ ≤ s → s ≤ Real.pi / 4 →
        θ / Real.pi ≤ Real.sin s * Real.cos s ^ 2)
    ∧ (∀ θ s : ℝ, Real.pi / 4 ≤ s → s ≤ θ → θ < Real.pi / 2 →
        (2 * Real.sqrt 2 / Real.pi ^ 2) * (Real.pi / 2 - θ) ^ 2
          ≤ Real.sin s * Real.cos s ^ 2) := by
  constructor
  · -- First half: `0 < θ ≤ s ≤ π/4`.  Jordan gives `sin s ≥ 2s/π` and monotonicity of
    -- `cos` on `[0, π/2]` gives `cos s ≥ cos (π/4) = √2/2`, whence `cos s ^ 2 ≥ 1/2`.
    intro θ s hθ hθs hs
    have hpi : 0 < Real.pi := Real.pi_pos
    have hs0 : 0 ≤ s := le_trans (le_of_lt hθ) hθs
    have hs_pi2 : s ≤ Real.pi / 2 := by linarith
    have hsin : 2 / Real.pi * s ≤ Real.sin s := Real.mul_le_sin hs0 hs_pi2
    have hcos_le : Real.cos (Real.pi / 4) ≤ Real.cos s :=
      Real.cos_le_cos_of_nonneg_of_le_pi hs0 (by linarith) hs
    rw [Real.cos_pi_div_four] at hcos_le
    have h1 : 0 ≤ Real.sqrt 2 / 2 := by positivity
    have hsq : (Real.sqrt 2 / 2) ^ 2 = (1 : ℝ) / 2 := by
      rw [div_pow, Real.sq_sqrt (by norm_num)]
      norm_num
    have hcos2 : (1 : ℝ) / 2 ≤ Real.cos s ^ 2 := by
      rw [← hsq]
      exact pow_le_pow_left₀ h1 hcos_le 2
    have hprod : (2 / Real.pi * s) * (1 / 2) ≤ Real.sin s * Real.cos s ^ 2 := by
      refine mul_le_mul hsin hcos2 (by norm_num) ?_
      exact Real.sin_nonneg_of_nonneg_of_le_pi hs0 (by linarith)
    have heq : (2 / Real.pi * s) * (1 / 2) = s / Real.pi := by ring
    calc θ / Real.pi ≤ s / Real.pi := div_le_div_of_nonneg_right hθs (le_of_lt hpi)
      _ = (2 / Real.pi * s) * (1 / 2) := heq.symm
      _ ≤ Real.sin s * Real.cos s ^ 2 := hprod
  · -- Second half: `π/4 ≤ s ≤ θ < π/2`.  Put `t = π/2 - s`, so `π/2 - θ ≤ t ≤ π/4` and
    -- `sin s cos²s = cos t sin²t`; Jordan gives `sin t ≥ 2t/π`, monotonicity `cos t ≥ √2/2`.
    intro θ s hs hθs hθ
    have hpi : 0 < Real.pi := Real.pi_pos
    set t := Real.pi / 2 - s with ht
    have ht0 : 0 ≤ t := by rw [ht]; linarith
    have htp4 : t ≤ Real.pi / 4 := by rw [ht]; linarith
    have htp2 : t ≤ Real.pi / 2 := by linarith
    have hsin_t : 2 / Real.pi * t ≤ Real.sin t := Real.mul_le_sin ht0 htp2
    have hcos_t : Real.sqrt 2 / 2 ≤ Real.cos t := by
      have h := Real.cos_le_cos_of_nonneg_of_le_pi ht0 (by linarith) htp4
      rwa [Real.cos_pi_div_four] at h
    have hdelta0 : 0 ≤ Real.pi / 2 - θ := by linarith
    have htdelta : Real.pi / 2 - θ ≤ t := by rw [ht]; linarith
    have hsin2 : (2 / Real.pi * t) ^ 2 ≤ Real.sin t ^ 2 :=
      pow_le_pow_left₀ (by positivity) hsin_t 2
    have hcos_t0 : 0 ≤ Real.cos t :=
      Real.cos_nonneg_of_mem_Icc (by constructor <;> linarith)
    have hprod : (Real.sqrt 2 / 2) * (2 / Real.pi * t) ^ 2 ≤ Real.cos t * Real.sin t ^ 2 :=
      mul_le_mul hcos_t hsin2 (by positivity) hcos_t0
    have hrewrite : Real.sin s * Real.cos s ^ 2 = Real.cos t * Real.sin t ^ 2 := by
      rw [ht, Real.cos_pi_div_two_sub, Real.sin_pi_div_two_sub]
    rw [hrewrite]
    calc (2 * Real.sqrt 2 / Real.pi ^ 2) * (Real.pi / 2 - θ) ^ 2
        ≤ (2 * Real.sqrt 2 / Real.pi ^ 2) * t ^ 2 :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hdelta0 htdelta 2) (by positivity)
      _ = (Real.sqrt 2 / 2) * (2 / Real.pi * t) ^ 2 := by ring
      _ ≤ Real.cos t * Real.sin t ^ 2 := hprod

end Work.FTS.EllipticEst.H2W.Lzb
