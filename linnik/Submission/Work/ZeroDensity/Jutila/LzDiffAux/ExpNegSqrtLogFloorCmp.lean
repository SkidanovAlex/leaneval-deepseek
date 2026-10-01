import Mathlib

namespace Work.ZeroDensity.Jutila.LzDiffAux

/-- For `0 ≤ v ≤ u`, the difference of the square roots is bounded by the square
root of the difference: this is the subadditivity of `Real.sqrt` rewritten. -/
private lemma sqrt_le_add_sqrt_sub {u v : ℝ} (hv : 0 ≤ v) (huv : v ≤ u) :
    Real.sqrt u ≤ Real.sqrt v + Real.sqrt (u - v) := by
  rw [Real.sqrt_le_iff]
  refine ⟨add_nonneg (Real.sqrt_nonneg v) (Real.sqrt_nonneg _), ?_⟩
  have h1 : (Real.sqrt v) ^ 2 = v := Real.sq_sqrt hv
  have h2 : (Real.sqrt (u - v)) ^ 2 = u - v := Real.sq_sqrt (by linarith)
  have h3 : 0 ≤ Real.sqrt v * Real.sqrt (u - v) :=
    mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  nlinarith [h1, h2, h3]

/-- Comparison of the "exponentially small" weights `exp (-(c √(log x)))` at
`x = a · d · ⌊T/d⌋` and `x = a · T`: since `d · ⌊T/d⌋` is within a factor `2` of `T`,
their logarithms differ by at most `log 2 < 1`, and the factor `exp c` absorbs the
resulting discrepancy of the square roots. -/
theorem ExpNegSqrtLogFloorCmp (c : ℝ) (hc : 0 < c) (a : ℝ) (ha : 1 ≤ a) (d T : ℕ) (hd : 1 ≤ d)
    (hdT : d ≤ T) :
    Real.exp (-(c * Real.sqrt (Real.log (a * (d : ℝ) * ((T / d : ℕ) : ℝ)))))
      ≤ Real.exp c * Real.exp (-(c * Real.sqrt (Real.log (a * (T : ℝ))))) := by
  have hd1 : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hdT' : (d : ℝ) ≤ (T : ℝ) := by exact_mod_cast hdT
  have hT1 : (1 : ℝ) ≤ (T : ℝ) := le_trans hd1 hdT'
  have hN1 : 1 ≤ T / d := (Nat.one_le_div_iff (by omega)).mpr hdT
  have hN1' : (1 : ℝ) ≤ ((T / d : ℕ) : ℝ) := by exact_mod_cast hN1
  have ha0 : (0 : ℝ) ≤ a := le_trans zero_le_one ha
  -- positivity / lower bounds of the two arguments of the logarithms
  have had : (1 : ℝ) ≤ a * (d : ℝ) := by
    have h := mul_le_mul ha hd1 zero_le_one (le_trans zero_le_one ha)
    simpa using h
  have hA1 : (1 : ℝ) ≤ a * (d : ℝ) * ((T / d : ℕ) : ℝ) := by
    have h := mul_le_mul had hN1' zero_le_one (le_trans zero_le_one had)
    simpa using h
  have hB1 : (1 : ℝ) ≤ a * (T : ℝ) := by
    have h := mul_le_mul ha hT1 zero_le_one (le_trans zero_le_one ha)
    simpa using h
  have hApos : 0 < a * (d : ℝ) * ((T / d : ℕ) : ℝ) := lt_of_lt_of_le zero_lt_one hA1
  have hBpos : 0 < a * (T : ℝ) := lt_of_lt_of_le zero_lt_one hB1
  -- `d * (T / d) ≤ T`
  have hdN : d * (T / d) ≤ T := by
    rw [Nat.mul_comm]; exact Nat.div_mul_le_self T d
  have hdN' : (d : ℝ) * ((T / d : ℕ) : ℝ) ≤ (T : ℝ) := by exact_mod_cast hdN
  have hAB : a * (d : ℝ) * ((T / d : ℕ) : ℝ) ≤ a * (T : ℝ) := by
    have h := mul_le_mul_of_nonneg_left hdN' ha0
    nlinarith [h]
  -- `T ≤ 2 * (d * (T / d))`, i.e. the floor loses at most a factor `2`
  have hT2 : T ≤ 2 * (d * (T / d)) := by
    have hdiv := Nat.div_add_mod T d
    have hmod := Nat.mod_lt T (show 0 < d by omega)
    have hdX : d ≤ d * (T / d) := by simpa using Nat.mul_le_mul_left d hN1
    omega
  have hT2' : (T : ℝ) ≤ 2 * ((d : ℝ) * ((T / d : ℕ) : ℝ)) := by exact_mod_cast hT2
  have hB2A : a * (T : ℝ) ≤ 2 * (a * (d : ℝ) * ((T / d : ℕ) : ℝ)) := by
    have h := mul_le_mul_of_nonneg_left hT2' ha0
    nlinarith [h]
  -- monotonicity of the logarithms
  have hlogmono : Real.log (a * (d : ℝ) * ((T / d : ℕ) : ℝ)) ≤ Real.log (a * (T : ℝ)) :=
    Real.log_le_log hApos hAB
  have hlogA0 : 0 ≤ Real.log (a * (d : ℝ) * ((T / d : ℕ) : ℝ)) := Real.log_nonneg hA1
  have hlogdiff :
      Real.log (a * (T : ℝ)) - Real.log (a * (d : ℝ) * ((T / d : ℕ) : ℝ)) ≤ Real.log 2 := by
    have h2A : Real.log (2 * (a * (d : ℝ) * ((T / d : ℕ) : ℝ)))
        = Real.log 2 + Real.log (a * (d : ℝ) * ((T / d : ℕ) : ℝ)) :=
      Real.log_mul (by norm_num) (ne_of_gt hApos)
    have hle : Real.log (a * (T : ℝ)) ≤ Real.log (2 * (a * (d : ℝ) * ((T / d : ℕ) : ℝ))) :=
      Real.log_le_log hBpos hB2A
    linarith
  -- the square roots differ by at most `1`
  have hsub : Real.sqrt (Real.log (a * (T : ℝ))) ≤
      Real.sqrt (Real.log (a * (d : ℝ) * ((T / d : ℕ) : ℝ)))
        + Real.sqrt (Real.log (a * (T : ℝ)) - Real.log (a * (d : ℝ) * ((T / d : ℕ) : ℝ))) :=
    sqrt_le_add_sqrt_sub hlogA0 hlogmono
  have hdiff_le : Real.sqrt (Real.log (a * (T : ℝ)))
      - Real.sqrt (Real.log (a * (d : ℝ) * ((T / d : ℕ) : ℝ))) ≤ 1 := by
    have h1 : Real.sqrt (Real.log (a * (T : ℝ)) - Real.log (a * (d : ℝ) * ((T / d : ℕ) : ℝ)))
        ≤ Real.sqrt (Real.log 2) := Real.sqrt_le_sqrt hlogdiff
    have h2 : Real.sqrt (Real.log 2) ≤ 1 := by
      have hlog2 : Real.log 2 ≤ 1 := by linarith [Real.log_two_lt_d9]
      calc Real.sqrt (Real.log 2) ≤ Real.sqrt 1 := Real.sqrt_le_sqrt hlog2
        _ = 1 := Real.sqrt_one
    linarith
  -- exponent comparison
  have hkey : -(c * Real.sqrt (Real.log (a * (d : ℝ) * ((T / d : ℕ) : ℝ))))
      ≤ c - c * Real.sqrt (Real.log (a * (T : ℝ))) := by
    have h := mul_le_mul_of_nonneg_left hdiff_le (le_of_lt hc)
    nlinarith [h]
  calc Real.exp (-(c * Real.sqrt (Real.log (a * (d : ℝ) * ((T / d : ℕ) : ℝ)))))
      ≤ Real.exp (c - c * Real.sqrt (Real.log (a * (T : ℝ)))) := Real.exp_le_exp.mpr hkey
    _ = Real.exp c * Real.exp (-(c * Real.sqrt (Real.log (a * (T : ℝ))))) := by
        rw [sub_eq_add_neg, Real.exp_add]

end Work.ZeroDensity.Jutila.LzDiffAux
