import Mathlib
import Submission.Work.RHContract.A.regionII.abdefs
import Submission.Work.RHContract.A.regionII.abel_h_upper
import Submission.Work.RHContract.A.regionII.abel_hsqrt_upper

namespace Work.RHContract.A.regionII

open MeasureTheory

/-!
# Region II: the Abel-kernel bounds behind `ab_piece`

With `uAb t = 1/(t log t)`, `chAb t = (2 + 1/log t)/log t` and the Abel kernel
`K t = (2 log t + 1)/(t³ (log t)²) = -d/dt (1/(t² log t))`, this file assembles
```
c·C₁ − d·C₂ − e·C₃ ≤ ∫_a^b K t · θ t
```
out of the three elementary integral estimates

* `abKt_lower` (proved below): `∫_a^b K t · t dt ≥ 2(u a − u b) − (u a − u b)/(log a + 1)`;
* `abel_h_upper` (imported): `∫_a^b K t dt ≤ χ a/2 · (a⁻² − b⁻²)`;
* `abel_hsqrt_upper` (imported): `∫_a^b K t · √t dt ≤ χ a · (2/3) · (a^{−3/2} − b^{−3/2})`,

from the pointwise lower bound `θ t ≥ c t − d − e √t` on `[a,b]` (with `c,d,e ≥ 0`).
-/

/-- `2 (u a − u b) − (u a − u b)/(log a + 1) ≤ ∫_a^b K t · t` for `2 ≤ a ≤ b`,
where `u t = uAb t = 1/(t log t)` and `K t = (2 log t + 1)/(t³ (log t)²)`.

Since `t·K t = 2·G t − 1/(t² log²t)` with `G t = (log t + 1)/(t² log²t)`, and
`−1/(t log t)` is an antiderivative of `G`, the claim is equivalent to the
integrand-wise inequality `1/(t²log²t) ≤ (log t + 1)/((log a + 1) t² log²t)`. -/
lemma abKt_lower {a b : ℝ} (ha : 2 ≤ a) (hab : a ≤ b) :
    2 * (Work.RHContract.A.RegionII.uAb a - Work.RHContract.A.RegionII.uAb b)
      - (Work.RHContract.A.RegionII.uAb a - Work.RHContract.A.RegionII.uAb b) / (Real.log a + 1)
    ≤ ∫ t in a..b, ((2 * Real.log t + 1)/(t^3*(Real.log t)^2)) * t := by
  have ha1 : 1 < a := by linarith
  have ha0 : 0 < a := by linarith
  have hla' : 0 < Real.log a + 1 := by
    have := Real.log_pos ha1; linarith
  have hlogc : ContinuousOn Real.log (Set.Icc a b) :=
    Real.continuousOn_log.mono (fun x hx => by
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
      exact ne_of_gt (by linarith [hx.1, ha0]))
  have hdenc : ContinuousOn (fun x : ℝ => x^2*(Real.log x)^2) (Set.Icc a b) :=
    (continuousOn_id.pow 2).mul (hlogc.pow 2)
  have hdenne : ∀ x ∈ Set.Icc a b, x^2*(Real.log x)^2 ≠ 0 := by
    intro x hx
    have hx0 : 0 < x := by linarith [hx.1, ha0]
    have hlx : 0 < Real.log x := Real.log_pos (by linarith [hx.1, ha1])
    exact mul_ne_zero (pow_ne_zero 2 (ne_of_gt hx0)) (pow_ne_zero 2 (ne_of_gt hlx))
  have hcontG : ContinuousOn (fun t : ℝ => (Real.log t + 1)/(t^2*(Real.log t)^2)) (Set.uIcc a b) := by
    rw [Set.uIcc_of_le hab]
    exact (hlogc.add continuousOn_const).div hdenc hdenne
  have hGint : IntervalIntegrable (fun t : ℝ => (Real.log t + 1)/(t^2*(Real.log t)^2)) volume a b :=
    hcontG.intervalIntegrable
  have hcontI : ContinuousOn (fun t : ℝ => 1/(t^2*(Real.log t)^2)) (Set.uIcc a b) := by
    rw [Set.uIcc_of_le hab]
    exact continuousOn_const.div hdenc hdenne
  have hIint : IntervalIntegrable (fun t : ℝ => 1/(t^2*(Real.log t)^2)) volume a b :=
    hcontI.intervalIntegrable
  have hderiv : ∀ x ∈ Set.uIcc a b, HasDerivAt (fun t : ℝ => -((t * Real.log t)⁻¹))
      ((Real.log x + 1)/(x^2*(Real.log x)^2)) x := by
    intro x hx
    rw [Set.uIcc_of_le hab] at hx
    have hx1 : 1 < x := lt_of_lt_of_le ha1 hx.1
    have hx0 : x ≠ 0 := by linarith
    have hlx : Real.log x ≠ 0 := ne_of_gt (Real.log_pos hx1)
    have htm : HasDerivAt (fun t : ℝ => t * Real.log t) (Real.log x + 1) x := by
      have h := (hasDerivAt_id x).mul (Real.hasDerivAt_log hx0)
      have hv : (1:ℝ) * Real.log x + id x * x⁻¹ = Real.log x + 1 := by
        have hid : (id x : ℝ) = x := rfl
        rw [one_mul, hid, mul_inv_cancel₀ hx0]
      rw [hv] at h
      exact h
    have hp : HasDerivAt (fun t : ℝ => (t * Real.log t)⁻¹) (-(Real.log x + 1)/(x*Real.log x)^2) x :=
      htm.inv (mul_ne_zero hx0 hlx)
    have hA : HasDerivAt (fun t : ℝ => -((t * Real.log t)⁻¹)) ((Real.log x + 1)/(x*Real.log x)^2) x := by
      have hd : (-(-(Real.log x + 1)/(x*Real.log x)^2)) = ((Real.log x + 1)/(x*Real.log x)^2) := by ring
      exact (hp.neg).congr_deriv hd
    simpa [mul_pow] using hA
  have hGa : (∫ t in a..b, (Real.log t + 1)/(t^2*(Real.log t)^2))
      = 1/(a*Real.log a) - 1/(b*Real.log b) := by
    have key := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hGint
    rw [key]
    simp only [one_div]
    ring
  have hF1 : (∫ t in a..b, ((2*Real.log t+1)/(t^3*(Real.log t)^2)) * t)
      = 2*(1/(a*Real.log a) - 1/(b*Real.log b)) - ∫ t in a..b, 1/(t^2*(Real.log t)^2) := by
    have hcongr : (∫ t in a..b, ((2*Real.log t+1)/(t^3*(Real.log t)^2)) * t)
        = ∫ t in a..b, (2 * ((Real.log t + 1)/(t^2*(Real.log t)^2)) - 1/(t^2*(Real.log t)^2)) := by
      apply intervalIntegral.integral_congr
      intro t ht
      rw [Set.uIcc_of_le hab] at ht
      have ht0 : 0 < t := by linarith [ht.1, ha0]
      have hlt : Real.log t ≠ 0 := ne_of_gt (Real.log_pos (by linarith [ht.1, ha1]))
      field_simp
      ring
    rw [hcongr, intervalIntegral.integral_sub (hGint.const_mul 2) hIint,
        intervalIntegral.integral_const_mul, hGa]
  have hF2 : (∫ t in a..b, 1/(t^2*(Real.log t)^2))
      ≤ (1/(a*Real.log a) - 1/(b*Real.log b))/(Real.log a + 1) := by
    have hpt : ∀ t ∈ Set.Icc a b,
        1/(t^2*(Real.log t)^2) ≤ (1/(Real.log a + 1)) * ((Real.log t + 1)/(t^2*(Real.log t)^2)) := by
      intro t ht
      have ht2 : (0:ℝ) < t^2*(Real.log t)^2 := by
        have ht0 : 0 < t := by linarith [ht.1, ha0]
        have hlt : 0 < Real.log t := Real.log_pos (by linarith [ht.1, ha1])
        positivity
      have hle : Real.log a ≤ Real.log t := Real.log_le_log ha0 ht.1
      have h : (1:ℝ) ≤ (Real.log t + 1)/(Real.log a + 1) := by
        rw [le_div_iff₀ hla']; linarith
      have key := div_le_div_of_nonneg_right h ht2.le
      have hrw : ((Real.log t + 1)/(Real.log a + 1))/(t^2*(Real.log t)^2)
          = (1/(Real.log a + 1)) * ((Real.log t + 1)/(t^2*(Real.log t)^2)) := by
        field_simp
      rwa [hrw] at key
    have hmono := intervalIntegral.integral_mono_on hab hIint (hGint.const_mul (1/(Real.log a+1))) hpt
    rw [intervalIntegral.integral_const_mul, hGa] at hmono
    have heq : (1/(Real.log a + 1)) * (1/(a*Real.log a) - 1/(b*Real.log b))
        = (1/(a*Real.log a) - 1/(b*Real.log b))/(Real.log a + 1) := by
      rw [div_eq_mul_inv]; ring
    rwa [heq] at hmono
  simp only [Work.RHContract.A.RegionII.uAb]
  linarith [hF1, hF2]

lemma ab_piece {a b c d e : ℝ} (ha : 2 ≤ a) (hab : a ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (he : 0 ≤ e)
    (hθ : ∀ t ∈ Set.Icc a b, c * t - d - e * Real.sqrt t ≤ Chebyshev.theta t) :
    c * (2 * (Work.RHContract.A.RegionII.uAb a - Work.RHContract.A.RegionII.uAb b)
          - (Work.RHContract.A.RegionII.uAb a - Work.RHContract.A.RegionII.uAb b) / (Real.log a + 1))
        - d * (Work.RHContract.A.RegionII.chAb a / 2 * (1 / a ^ 2 - 1 / b ^ 2))
        - e * (Work.RHContract.A.RegionII.chAb a * (2 / 3) * (1 / (a * Real.sqrt a) - 1 / (b * Real.sqrt b)))
      ≤ ∫ t in a..b, ((2 * Real.log t + 1) / (t ^ 3 * (Real.log t) ^ 2)) * Chebyshev.theta t := by
  have ha1 : 1 < a := by linarith
  have h1 := abKt_lower ha hab
  have h2 : ∫ t in a..b, ((2 * Real.log t + 1)/(t^3*(Real.log t)^2))
      ≤ Work.RHContract.A.RegionII.chAb a/2 * (1/a^2 - 1/b^2) := by
    have h := abel_h_upper (a := a) (b := b) (by linarith) hab
    simpa only [Work.RHContract.A.RegionII.chAb] using h
  have h3 : ∫ t in a..b, ((2 * Real.log t + 1)/(t^3*(Real.log t)^2)) * Real.sqrt t
      ≤ Work.RHContract.A.RegionII.chAb a * (2/3) * (1/(a*Real.sqrt a) - 1/(b*Real.sqrt b)) := by
    have h := abel_hsqrt_upper (a := a) (b := b) (by linarith) hab
    simpa only [Work.RHContract.A.RegionII.chAb] using h
  have hKnn : ∀ t ∈ Set.Icc a b, 0 ≤ (2 * Real.log t + 1)/(t^3*(Real.log t)^2) := by
    intro t ht
    have hlt : 0 < Real.log t := Real.log_pos (by linarith [ht.1, ha1])
    have hnum : 0 ≤ 2 * Real.log t + 1 := by linarith
    have hden : 0 < t^3*(Real.log t)^2 := by
      have ht0 : 0 < t := by linarith [ht.1]
      positivity
    exact div_nonneg hnum hden.le
  have hKcont : ContinuousOn (fun t : ℝ => (2 * Real.log t + 1)/(t^3*(Real.log t)^2)) (Set.uIcc a b) := by
    rw [Set.uIcc_of_le hab]
    have hlogc : ContinuousOn Real.log (Set.Icc a b) :=
      Real.continuousOn_log.mono (fun x hx => by
        simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
        exact ne_of_gt (by linarith [hx.1]))
    have hnum : ContinuousOn (fun x : ℝ => 2*Real.log x + 1) (Set.Icc a b) :=
      (hlogc.const_mul 2).add continuousOn_const
    have hden : ContinuousOn (fun x : ℝ => x^3*(Real.log x)^2) (Set.Icc a b) :=
      (continuousOn_id.pow 3).mul (hlogc.pow 2)
    refine hnum.div hden (fun x hx => ?_)
    have hx0 : 0 < x := by linarith [hx.1]
    have hlx : 0 < Real.log x := Real.log_pos (by linarith [hx.1, ha1])
    exact mul_ne_zero (pow_ne_zero 3 (ne_of_gt hx0)) (pow_ne_zero 2 (ne_of_gt hlx))
  have htc : ContinuousOn (fun t : ℝ => ((2*Real.log t+1)/(t^3*(Real.log t)^2)) * t) (Set.uIcc a b) :=
    hKcont.mul continuousOn_id
  have hsc : ContinuousOn (fun t : ℝ => ((2*Real.log t+1)/(t^3*(Real.log t)^2)) * Real.sqrt t) (Set.uIcc a b) :=
    hKcont.mul Real.continuous_sqrt.continuousOn
  have hfun_cont : ContinuousOn
      (fun t : ℝ => ((2*Real.log t+1)/(t^3*(Real.log t)^2)) * (c*t - d - e*Real.sqrt t)) (Set.uIcc a b) :=
    hKcont.mul (((continuousOn_id.const_mul c).sub continuousOn_const).sub
      (continuousOn_const.mul Real.continuous_sqrt.continuousOn))
  have hint1 : IntervalIntegrable
      (fun t : ℝ => ((2*Real.log t+1)/(t^3*(Real.log t)^2)) * (c*t - d - e*Real.sqrt t)) volume a b :=
    hfun_cont.intervalIntegrable
  have hint2 : IntervalIntegrable
      (fun t : ℝ => ((2*Real.log t+1)/(t^3*(Real.log t)^2)) * Chebyshev.theta t) volume a b :=
    Chebyshev.theta_mono.intervalIntegrable.continuousOn_mul hKcont
  have hmono := intervalIntegral.integral_mono_on hab hint1 hint2
    (fun t ht => mul_le_mul_of_nonneg_left (hθ t ht) (hKnn t ht))
  have hExp : (∫ t in a..b, ((2*Real.log t+1)/(t^3*(Real.log t)^2)) * (c*t - d - e*Real.sqrt t))
      = c * (∫ t in a..b, ((2*Real.log t+1)/(t^3*(Real.log t)^2)) * t)
        - d * (∫ t in a..b, ((2*Real.log t+1)/(t^3*(Real.log t)^2)))
        - e * (∫ t in a..b, ((2*Real.log t+1)/(t^3*(Real.log t)^2)) * Real.sqrt t) := by
    have hcongr : (∫ t in a..b, ((2*Real.log t+1)/(t^3*(Real.log t)^2)) * (c*t - d - e*Real.sqrt t))
        = ∫ t in a..b, (c * (((2*Real.log t+1)/(t^3*(Real.log t)^2)) * t)
            - d * ((2*Real.log t+1)/(t^3*(Real.log t)^2))
            - e * (((2*Real.log t+1)/(t^3*(Real.log t)^2)) * Real.sqrt t)) := by
      apply intervalIntegral.integral_congr
      intro t ht
      ring
    rw [hcongr,
      intervalIntegral.integral_sub ((htc.intervalIntegrable.const_mul c).sub (hKcont.intervalIntegrable.const_mul d))
        (hsc.intervalIntegrable.const_mul e),
      intervalIntegral.integral_sub (htc.intervalIntegrable.const_mul c) (hKcont.intervalIntegrable.const_mul d),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul]
  have hc1 := mul_le_mul_of_nonneg_left h1 hc
  have hc2 : - (d * (Work.RHContract.A.RegionII.chAb a / 2 * (1 / a ^ 2 - 1 / b ^ 2)))
      ≤ - (d * (∫ t in a..b, ((2*Real.log t+1)/(t^3*(Real.log t)^2)))) :=
    neg_le_neg (mul_le_mul_of_nonneg_left h2 hd)
  have hc3 : - (e * (Work.RHContract.A.RegionII.chAb a * (2/3) * (1/(a*Real.sqrt a) - 1/(b*Real.sqrt b))))
      ≤ - (e * (∫ t in a..b, ((2*Real.log t+1)/(t^3*(Real.log t)^2)) * Real.sqrt t)) :=
    neg_le_neg (mul_le_mul_of_nonneg_left h3 he)
  linarith [hmono, hExp, hc1, hc2, hc3]

end Work.RHContract.A.regionII
