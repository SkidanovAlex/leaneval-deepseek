import Mathlib

namespace Work.ZeroDensity.LogFree

open MeasureTheory

/-- Real fundamental-theorem-of-calculus identity: for a positive base `t` and `r ≥ 0`,
`∫_0^r log t · t ^ b db = t ^ r - 1`. -/
private lemma integral_log_mul_rpow {t r : ℝ} (ht : 0 < t) (hr : 0 ≤ r) :
    ∫ b in (0)..r, Real.log t * t ^ b = t ^ r - 1 := by
  have hcont : ContinuousOn (fun b : ℝ => t ^ b) (Set.Icc 0 r) :=
    (Real.continuous_const_rpow ht.ne').continuousOn
  have hderiv : ∀ x ∈ Set.Ioo (0 : ℝ) r, HasDerivAt (fun b : ℝ => t ^ b) (Real.log t * t ^ x) x := by
    intro x _
    have h := (Real.hasStrictDerivAt_const_rpow ht x).hasDerivAt
    simpa [mul_comm] using h
  have hint : IntervalIntegrable (fun b : ℝ => Real.log t * t ^ b) volume 0 r := by
    apply Continuous.intervalIntegrable
    exact continuous_const.mul (Real.continuous_const_rpow ht.ne')
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hr hcont hderiv hint
  simpa [Real.rpow_zero] using h

/-- Complexification of `integral_log_mul_rpow`. -/
private lemma integral_log_mul_rpow_complex {t r : ℝ} (ht : 0 < t) (hr : 0 ≤ r) :
    ∫ b in (0)..r, ((Real.log t : ℝ) : ℂ) * ((t ^ b : ℝ) : ℂ) = ((t ^ r - 1 : ℝ) : ℂ) := by
  have hreal := integral_log_mul_rpow ht hr
  have h1 : ∫ b in (0)..r, ((Real.log t : ℝ) : ℂ) * ((t ^ b : ℝ) : ℂ)
      = ∫ b in (0)..r, ((Real.log t * t ^ b : ℝ) : ℂ) := by
    apply intervalIntegral.integral_congr
    intro b _
    exact (Complex.ofReal_mul _ _).symm
  rw [h1, intervalIntegral.integral_ofReal, hreal]

/-- Fundamental-theorem-of-calculus identity behind the freezing of amplitudes: for a positive base
`t` and exponents `0 ≤ p i ≤ q`, the "freeze error" `t ^ p - 1` is the integral over `b ∈ [0,q]` of
`1_{b ≤ p} · log t · t ^ b`, so that the amplitude at level `p` is expanded in the frozen amplitude
at level `b`.  Complex coefficients `c i` are carried along. -/
theorem FreezeRpowIdentity {ι : Type*} [Fintype ι] (c : ι → ℂ) (p : ι → ℝ) {t q : ℝ}
    (ht : 0 < t) (hq : 0 ≤ q) (hp0 : ∀ i, 0 ≤ p i) (hpq : ∀ i, p i ≤ q) :
    (∑ i, c i * (((t ^ (p i) - 1 : ℝ)) : ℂ))
      = ∫ b in (0)..q,
          ((Real.log t : ℝ) : ℂ) * (∑ i, (if b ≤ p i then c i else 0) * (((t ^ b : ℝ)) : ℂ)) := by
  -- each individual term `(log t) · 1_{b ≤ p i} · t ^ b` is interval integrable on `[0, q]`
  have integrable_term : ∀ i, IntervalIntegrable
      (fun b : ℝ => ((Real.log t : ℝ) : ℂ)
        * ((if b ≤ p i then c i else 0) * (((t ^ b : ℝ)) : ℂ))) volume 0 q := by
    intro i
    have hpt : ∀ b, ((Real.log t : ℝ) : ℂ)
          * ((if b ≤ p i then c i else 0) * (((t ^ b : ℝ)) : ℂ))
        = (Set.Iic (p i)).indicator
            (fun b => ((Real.log t : ℝ) : ℂ) * c i * (((t ^ b : ℝ)) : ℂ)) b := by
      intro b
      by_cases h : b ≤ p i
      · simp [h, mul_assoc]
      · simp [h]
    have hfun : (fun b : ℝ => ((Real.log t : ℝ) : ℂ)
          * ((if b ≤ p i then c i else 0) * (((t ^ b : ℝ)) : ℂ)))
        = fun b : ℝ => (Set.Iic (p i)).indicator
            (fun b => ((Real.log t : ℝ) : ℂ) * c i * (((t ^ b : ℝ)) : ℂ)) b := funext hpt
    rw [hfun]
    constructor
    · apply MeasureTheory.IntegrableOn.indicator
      · have hcontfun : Continuous
            (fun b : ℝ => ((Real.log t : ℝ) : ℂ) * c i * (((t ^ b : ℝ)) : ℂ)) :=
          (continuous_const.mul continuous_const).mul
            (Complex.continuous_ofReal.comp (Real.continuous_const_rpow ht.ne'))
        exact (hcontfun.intervalIntegrable 0 q).1
      · exact measurableSet_Iic
    · rw [Set.Ioc_eq_empty (not_lt.mpr hq)]
      exact MeasureTheory.integrableOn_empty
  -- value of one frozen term
  have inteq : ∀ i, ∫ b in (0)..q, ((Real.log t : ℝ) : ℂ)
        * ((if b ≤ p i then c i else 0) * (((t ^ b : ℝ)) : ℂ))
      = c i * (((t ^ (p i) - 1 : ℝ)) : ℂ) := by
    intro i
    have hpt : ∀ b, ((Real.log t : ℝ) : ℂ)
          * ((if b ≤ p i then c i else 0) * (((t ^ b : ℝ)) : ℂ))
        = (Set.Iic (p i)).indicator
            (fun b => ((Real.log t : ℝ) : ℂ) * c i * (((t ^ b : ℝ)) : ℂ)) b := by
      intro b
      by_cases h : b ≤ p i
      · simp [h, mul_assoc]
      · simp [h]
    rw [intervalIntegral.integral_congr (fun b _ => hpt b)]
    rw [← Set.Iic_def (p i)]
    rw [intervalIntegral.integral_indicator (show p i ∈ Set.Icc (0 : ℝ) q from ⟨hp0 i, hpq i⟩)]
    have hpull : ∫ b in (0)..(p i), ((Real.log t : ℝ) : ℂ) * c i * (((t ^ b : ℝ)) : ℂ)
        = c i * ∫ b in (0)..(p i), ((Real.log t : ℝ) : ℂ) * (((t ^ b : ℝ)) : ℂ) := by
      rw [← intervalIntegral.integral_const_mul]
      apply intervalIntegral.integral_congr
      intro b _
      ring
    rw [hpull, integral_log_mul_rpow_complex ht (hp0 i)]
  -- pull the finite sum out of the integral and evaluate each term
  have hR : ∫ b in (0)..q, ((Real.log t : ℝ) : ℂ)
        * (∑ i, (if b ≤ p i then c i else 0) * (((t ^ b : ℝ)) : ℂ))
      = ∑ i, c i * (((t ^ (p i) - 1 : ℝ)) : ℂ) := by
    have h1 : ∫ b in (0)..q, ((Real.log t : ℝ) : ℂ)
          * (∑ i, (if b ≤ p i then c i else 0) * (((t ^ b : ℝ)) : ℂ))
        = ∫ b in (0)..q, ∑ i, ((Real.log t : ℝ) : ℂ)
            * ((if b ≤ p i then c i else 0) * (((t ^ b : ℝ)) : ℂ)) := by
      apply intervalIntegral.integral_congr
      intro b _
      exact Finset.mul_sum Finset.univ
        (fun i => (if b ≤ p i then c i else 0) * (((t ^ b : ℝ)) : ℂ)) ((Real.log t : ℝ) : ℂ)
    rw [h1, intervalIntegral.integral_finsetSum]
    · exact Finset.sum_congr rfl (fun i _ => inteq i)
    · intro i _
      exact integrable_term i
  exact hR.symm

end Work.ZeroDensity.LogFree
