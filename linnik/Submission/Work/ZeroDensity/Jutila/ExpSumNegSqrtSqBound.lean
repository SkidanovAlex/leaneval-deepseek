import Mathlib

namespace Work.ZeroDensity.Jutila

/-- The improper-feeling bound needed below: for `a > 0` and any `N`,
`∫_0^N exp(-a√x) dx ≤ 2/a²`.  The antiderivative of `exp(-a√x)` is
`-(2/a²)(1+a√x)exp(-a√x)`, which is nonpositive on `[0,∞)`; the Fundamental
Theorem of Calculus then gives the bound. -/
lemma expSqrtIntegralBound (a : ℝ) (ha : 0 < a) (x : ℕ) :
    (∫ t in (0:ℝ)..(x:ℝ), Real.exp (-(a * Real.sqrt t))) ≤ 2 / a^2 := by
  set F : ℝ → ℝ := fun y => (2 / a^2) * ((1 + a * Real.sqrt y) * Real.exp (-(a * Real.sqrt y))) with hFdef
  have hderiv : ∀ t ∈ Set.Ioo (0:ℝ) (x:ℝ), HasDerivAt F (-(Real.exp (-(a * Real.sqrt t)))) t := by
    intro t ht
    have ht' : 0 < t := ht.1
    have hsqrt : HasDerivAt (fun y : ℝ => Real.sqrt y) (1/(2*Real.sqrt t)) t :=
      Real.hasDerivAt_sqrt (ne_of_gt ht')
    have hu : HasDerivAt (fun y : ℝ => a * Real.sqrt y) (a * (1/(2*Real.sqrt t))) t :=
      hsqrt.const_mul a
    have h1u : HasDerivAt (fun y : ℝ => 1 + a * Real.sqrt y) (a * (1/(2*Real.sqrt t))) t :=
      hu.const_add 1
    have hexp : HasDerivAt (fun y : ℝ => Real.exp (-(a * Real.sqrt y)))
        (Real.exp (-(a*Real.sqrt t)) * (-(a*(1/(2*Real.sqrt t))))) t := hu.neg.exp
    have hprod := h1u.mul hexp
    have hF := hprod.const_mul (2/a^2)
    have hval : (2 / a^2) * ((a * (1/(2*Real.sqrt t))) * Real.exp (-(a*Real.sqrt t))
        + (1 + a*Real.sqrt t) * (Real.exp (-(a*Real.sqrt t)) * (-(a*(1/(2*Real.sqrt t))))))
        = -(Real.exp (-(a * Real.sqrt t))) := by
      have hs : Real.sqrt t ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr ht')
      field_simp
      ring
    rw [hval] at hF
    exact hF
  have hcont : ContinuousOn F (Set.Icc 0 (x:ℝ)) := by
    rw [hFdef]; fun_prop
  have hint : IntervalIntegrable (fun y => -(Real.exp (-(a * Real.sqrt y))))
      MeasureTheory.volume (0:ℝ) (x:ℝ) := by
    apply Continuous.intervalIntegrable; fun_prop
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le (a := (0:ℝ)) (b := (x:ℝ))
    (by positivity) hcont hderiv hint
  have hneg : (∫ t in (0:ℝ)..(x:ℝ), Real.exp (-(a * Real.sqrt t))) = -(F (x:ℝ) - F 0) := by
    have h := hFTC
    rw [intervalIntegral.integral_neg] at h
    linarith
  rw [hneg]
  have hF0 : F 0 = 2 / a^2 := by rw [hFdef]; simp
  have hFx : 0 ≤ F (x:ℝ) := by
    rw [hFdef]
    have : 0 ≤ (1 + a*Real.sqrt (x:ℝ)) := by
      have := Real.sqrt_nonneg (x:ℝ); nlinarith [ha.le, this]
    positivity
  rw [hF0]; linarith

/-- **Linnik (Jutila) exponential-square-root sum bound.**
For `a > 0` and every `J`, `∑_{k=0}^{J} exp(-a√k) ≤ 10 + 10/a²`. -/
theorem ExpSumNegSqrtSqBound {a : ℝ} (ha : 0 < a) (J : ℕ) :
    (∑ k ∈ Finset.range (J + 1), Real.exp (-(a * Real.sqrt (k : ℝ)))) ≤ 10 + 10 / a ^ 2 := by
  rw [Finset.sum_range_succ']
  have hsum : (∑ k ∈ Finset.range J,
      Real.exp (-(a * Real.sqrt (((k + 1 : ℕ) : ℝ))))) ≤ 2 / a^2 := by
    have hanti : AntitoneOn (fun x : ℝ => Real.exp (-(a * Real.sqrt x)))
        (Set.Icc 0 (0 + (J:ℝ))) := by
      intro x hx y hy hxy
      simp only [Set.mem_Icc] at hx hy
      apply Real.exp_le_exp.mpr
      apply neg_le_neg
      exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hxy) ha.le
    have h1 := hanti.sum_le_integral
    simp only [zero_add] at h1
    exact le_trans h1 (expSqrtIntegralBound a ha J)
  have h0 : Real.exp (-(a * Real.sqrt (((0:ℕ):ℝ)))) = 1 := by simp
  rw [h0]
  have h2 : (2:ℝ)/a^2 ≤ 10/a^2 := by
    have : (0:ℝ) < a^2 := by positivity
    gcongr; norm_num
  linarith [hsum, h2]

end Work.ZeroDensity.Jutila
