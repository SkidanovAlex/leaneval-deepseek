import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

namespace Commons.Analysis.Real

open MeasureTheory Set
open scoped Interval

/-- Derivative of the antiderivative `t ↦ (t log t)⁻¹`. -/
private lemma hasDerivAt_inv_mul_log {x : ℝ} (hx : x ≠ 0) (hlx : Real.log x ≠ 0) :
    HasDerivAt (fun t : ℝ => (t * Real.log t)⁻¹)
      (-((Real.log x + 1) / (x * Real.log x)^2)) x := by
  have hp1 : HasDerivAt (fun t : ℝ => t * Real.log t) (Real.log x + 1) x := by
    have h1 : HasDerivAt (fun t : ℝ => t) (1 : ℝ) x := hasDerivAt_id x
    have h2 : HasDerivAt (fun t : ℝ => Real.log t) x⁻¹ x := Real.hasDerivAt_log hx
    have h3 := h1.mul h2
    have hval : (1 : ℝ) * Real.log x + x * x⁻¹ = Real.log x + 1 := by
      rw [one_mul, mul_inv_cancel₀ hx]
    rw [hval] at h3
    exact h3
  exact (hp1.inv (mul_ne_zero hx hlx)).congr_deriv (by rw [neg_div])

/-- The two forms of the second summand agree. -/
private lemma pointwise_f2 {x : ℝ} (hx : x ≠ 0) :
    ((2 * Real.log x + 1) / (x^3 * (Real.log x)^2)) * x
      = (2 * Real.log x + 1) / (x^2 * (Real.log x)^2) := by
  field_simp

/-- `1/(x² log x)` splits as `(2 log x + 1)/(x² (log x)²) + ((x log x)⁻¹)'`. -/
private lemma pointwise_f1 {x : ℝ} (hx : x ≠ 0) (hlx : Real.log x ≠ 0) :
    1 / (x^2 * Real.log x)
      = (2 * Real.log x + 1) / (x^2 * (Real.log x)^2)
        + (-((Real.log x + 1) / (x * Real.log x)^2)) := by
  have h : (x * Real.log x)^2 = x^2 * (Real.log x)^2 := by ring
  rw [h]
  field_simp
  ring

/-- The boundary terms rewrite into the values of the antiderivative. -/
private lemma boundary_eq {n m : ℝ} (hn : 0 < n) (hm : 0 < m)
    (hln : Real.log n ≠ 0) (hlm : Real.log m ≠ 0) :
    (1 / (m^2 * Real.log m)) * m - (1 / (n^2 * Real.log n)) * n
      = (m * Real.log m)⁻¹ - (n * Real.log n)⁻¹ := by
  field_simp

theorem main_term_abel_identity {n m : ℝ} (hn : 1 < n) (hnm : n ≤ m) :
    (1/(m^2 * Real.log m)) * m - (1/(n^2 * Real.log n)) * n
      + ∫ t in Set.Ioc n m, ((2*Real.log t + 1)/(t^3 * (Real.log t)^2)) * t
      = ∫ t in n..m, 1/(t^2 * Real.log t) := by
  have hn0 : 0 < n := by linarith
  have hm1 : 1 < m := lt_of_lt_of_le hn hnm
  have hm0 : 0 < m := by linarith
  have hln : Real.log n ≠ 0 := ne_of_gt (Real.log_pos hn)
  have hlm : Real.log m ≠ 0 := ne_of_gt (Real.log_pos hm1)
  -- turn the `Ioc` integral on the left into an interval integral
  rw [← intervalIntegral.integral_of_le hnm]
  have hbound : (1 / (m^2 * Real.log m)) * m - (1 / (n^2 * Real.log n)) * n
      = (m * Real.log m)⁻¹ - (n * Real.log n)⁻¹ := boundary_eq hn0 hm0 hln hlm
  -- first rewrite the integrand of the second summand
  have hf2 : ∫ t in n..m, ((2*Real.log t + 1)/(t^3 * (Real.log t)^2)) * t
      = ∫ t in n..m, (2*Real.log t + 1)/(t^2 * (Real.log t)^2) := by
    apply intervalIntegral.integral_congr
    intro x hx
    rw [uIcc_of_le hnm] at hx
    have hx1 : 1 < x := lt_of_lt_of_le hn hx.1
    exact pointwise_f2 (by linarith)
  -- continuity of the two summands on `[n,m]`
  have hcont_f2c : ContinuousOn
      (fun t : ℝ => (2 * Real.log t + 1) / (t^2 * (Real.log t)^2)) (Icc n m) := by
    have hlog : ContinuousOn (fun t : ℝ => Real.log t) (Icc n m) :=
      Real.continuousOn_log.mono (fun t ht => by
        simp only [mem_compl_iff, mem_singleton_iff]
        have h1 : (1 : ℝ) < t := lt_of_lt_of_le hn ht.1
        linarith)
    have hid : ContinuousOn (fun t : ℝ => t) (Icc n m) := continuousOn_id
    have hnum : ContinuousOn (fun t : ℝ => 2 * Real.log t + 1) (Icc n m) :=
      (hlog.const_mul 2).add continuousOn_const
    have hden : ContinuousOn (fun t : ℝ => t^2 * (Real.log t)^2) (Icc n m) :=
      (hid.pow 2).mul (hlog.pow 2)
    exact hnum.div hden (fun t ht => by
      have h1 : (1 : ℝ) < t := lt_of_lt_of_le hn ht.1
      have ht0 : t ≠ 0 := by linarith
      have hl0 : Real.log t ≠ 0 := ne_of_gt (Real.log_pos h1)
      exact mul_ne_zero (pow_ne_zero 2 ht0) (pow_ne_zero 2 hl0))
  have hcont_g' : ContinuousOn
      (fun t : ℝ => -((Real.log t + 1) / (t * Real.log t)^2)) (Icc n m) := by
    have hlog : ContinuousOn (fun t : ℝ => Real.log t) (Icc n m) :=
      Real.continuousOn_log.mono (fun t ht => by
        simp only [mem_compl_iff, mem_singleton_iff]
        have h1 : (1 : ℝ) < t := lt_of_lt_of_le hn ht.1
        linarith)
    have hid : ContinuousOn (fun t : ℝ => t) (Icc n m) := continuousOn_id
    have htl : ContinuousOn (fun t : ℝ => t * Real.log t) (Icc n m) := hid.mul hlog
    have hnum : ContinuousOn (fun t : ℝ => Real.log t + 1) (Icc n m) :=
      hlog.add continuousOn_const
    have hq : ContinuousOn (fun t : ℝ => (Real.log t + 1) / (t * Real.log t)^2) (Icc n m) :=
      hnum.div (htl.pow 2) (fun t ht => by
        have h1 : (1 : ℝ) < t := lt_of_lt_of_le hn ht.1
        have ht0 : t ≠ 0 := by linarith
        have hl0 : Real.log t ≠ 0 := ne_of_gt (Real.log_pos h1)
        exact pow_ne_zero 2 (mul_ne_zero ht0 hl0))
    exact hq.neg
  have hf2c_int : IntervalIntegrable
      (fun t : ℝ => (2 * Real.log t + 1) / (t^2 * (Real.log t)^2)) volume n m :=
    hcont_f2c.intervalIntegrable_of_Icc hnm
  have hg'int : IntervalIntegrable
      (fun t : ℝ => -((Real.log t + 1) / (t * Real.log t)^2)) volume n m :=
    hcont_g'.intervalIntegrable_of_Icc hnm
  -- the fundamental theorem of calculus
  have hderiv : ∀ x ∈ uIcc n m, HasDerivAt (fun t : ℝ => (t * Real.log t)⁻¹)
      (-((Real.log x + 1) / (x * Real.log x)^2)) x := by
    intro x hx
    rw [uIcc_of_le hnm] at hx
    have hx1 : 1 < x := lt_of_lt_of_le hn hx.1
    exact hasDerivAt_inv_mul_log (by linarith) (ne_of_gt (Real.log_pos hx1))
  have hFTC : ∫ t in n..m, -((Real.log t + 1) / (t * Real.log t)^2)
      = (m * Real.log m)⁻¹ - (n * Real.log n)⁻¹ :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hg'int
  -- main identity
  have hf1 : ∫ t in n..m, 1/(t^2 * Real.log t)
      = (∫ t in n..m, (2*Real.log t + 1)/(t^2 * (Real.log t)^2))
        + ((m * Real.log m)⁻¹ - (n * Real.log n)⁻¹) := by
    have hpt : EqOn (fun t : ℝ => 1/(t^2 * Real.log t))
        (fun t : ℝ => (2*Real.log t + 1)/(t^2 * (Real.log t)^2)
          + (-((Real.log t + 1) / (t * Real.log t)^2))) (uIcc n m) := by
      intro x hx
      rw [uIcc_of_le hnm] at hx
      have hx1 : 1 < x := lt_of_lt_of_le hn hx.1
      exact pointwise_f1 (by linarith) (ne_of_gt (Real.log_pos hx1))
    rw [intervalIntegral.integral_congr hpt]
    rw [intervalIntegral.integral_add hf2c_int hg'int]
    rw [hFTC]
  rw [hf2, hf1, hbound]
  ring

end Commons.Analysis.Real