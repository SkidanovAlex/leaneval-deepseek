import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

namespace Commons.Analysis.Real

open scoped Interval
open MeasureTheory Set

/-- Derivative of the auxiliary antiderivative
`t ↦ -(t log t)⁻¹ + (log n)⁻² t⁻¹`. -/
lemma psi_hasDerivAt {n x : ℝ} (hx : 1 < x) :
    HasDerivAt (fun t => -((t * Real.log t)⁻¹) + ((Real.log n)^2)⁻¹ * t⁻¹)
      ((Real.log x + 1)/(x * Real.log x)^2 - ((Real.log n)^2)⁻¹ * (x^2)⁻¹) x := by
  have hx0 : x ≠ 0 := by linarith
  have hlx : Real.log x ≠ 0 := ne_of_gt (Real.log_pos hx)
  have hp1 : HasDerivAt (fun t : ℝ => t * Real.log t) (Real.log x + 1) x := by
    have h1 : HasDerivAt (fun t : ℝ => t) (1:ℝ) x := hasDerivAt_id x
    have h2 : HasDerivAt (fun t : ℝ => Real.log t) (x)⁻¹ x := Real.hasDerivAt_log hx0
    have h3 := h1.mul h2
    have hval : (1:ℝ) * Real.log x + x * (x)⁻¹ = Real.log x + 1 := by
      rw [one_mul, mul_inv_cancel₀ hx0]
    rw [hval] at h3
    exact h3
  have hp1' : HasDerivAt (fun t => (t * Real.log t)⁻¹)
      (-(Real.log x + 1)/(x * Real.log x)^2) x :=
    hp1.inv (mul_ne_zero hx0 hlx)
  have hA : HasDerivAt (fun t => -((t * Real.log t)⁻¹))
      ((Real.log x + 1)/(x * Real.log x)^2) x := by
    have hd : (-(-(Real.log x + 1)/(x * Real.log x)^2)) = ((Real.log x + 1)/(x * Real.log x)^2) := by
      ring
    exact (hp1'.neg).congr_deriv hd
  have hbase : HasDerivAt (fun t : ℝ => t⁻¹) (-(x^2)⁻¹) x := by
    have h : HasDerivAt (fun t : ℝ => t) (1:ℝ) x := hasDerivAt_id x
    have hd : (-1 / x^2) = -(x^2)⁻¹ := by rw [div_eq_mul_inv, neg_mul, one_mul]
    exact (h.inv hx0).congr_deriv hd
  have hB : HasDerivAt (fun t => ((Real.log n)^2)⁻¹ * t⁻¹)
      (((Real.log n)^2)⁻¹ * (-(x^2)⁻¹)) x :=
    HasDerivAt.const_mul ((Real.log n)^2)⁻¹ hbase
  have hgoal2 : ((Real.log x + 1)/(x * Real.log x)^2 + ((Real.log n)^2)⁻¹ * (-(x^2)⁻¹))
      = ((Real.log x + 1)/(x * Real.log x)^2 - ((Real.log n)^2)⁻¹ * (x^2)⁻¹) := by ring
  exact (hA.add hB).congr_deriv hgoal2

/-- Pointwise lower bound for the integrand. -/
lemma psi'_le_inv {n x : ℝ} (hn : 1 < n) (hx : n ≤ x) :
    (Real.log x + 1)/(x * Real.log x)^2 - ((Real.log n)^2)⁻¹ * (x^2)⁻¹
      ≤ 1/(x^2 * Real.log x) := by
  have hx1 : 1 < x := lt_of_lt_of_le hn hx
  have hxn0 : x ≠ 0 := by linarith
  have hln : Real.log n ≠ 0 := ne_of_gt (Real.log_pos hn)
  have hlx : Real.log x ≠ 0 := ne_of_gt (Real.log_pos hx1)
  have hle_log : Real.log n ≤ Real.log x := Real.log_le_log (by linarith) hx
  rw [← sub_nonneg]
  have key : 1/(x^2 * Real.log x)
      - ((Real.log x + 1)/(x * Real.log x)^2 - ((Real.log n)^2)⁻¹ * (x^2)⁻¹)
      = (1/x^2) * (1/(Real.log n)^2 - 1/(Real.log x)^2) := by
    field_simp
    ring
  rw [key]
  apply mul_nonneg
  · positivity
  · apply sub_nonneg.mpr
    apply one_div_le_one_div_of_le
    · positivity
    · exact pow_le_pow_left₀ (le_of_lt (Real.log_pos hn)) hle_log 2

theorem integral_inv_sq_log_lower {n m : ℝ} (hn : 1 < n) (hnm : n ≤ m) :
    ∫ t in n..m, 1/(t^2 * Real.log t)
      ≥ (1/(n * Real.log n)) * (1 - n / min m (n^2) - 1/(Real.log n)) := by
  have hln : Real.log n ≠ 0 := ne_of_gt (Real.log_pos hn)
  set P : ℝ → ℝ := fun t => (Real.log t + 1)/(t * Real.log t)^2 - ((Real.log n)^2)⁻¹ * (t^2)⁻¹
    with hP
  set psi : ℝ → ℝ := fun t => -((t * Real.log t)⁻¹) + ((Real.log n)^2)⁻¹ * t⁻¹ with hpsi
  -- continuity of the integrand
  have hFcont : ContinuousOn (fun t : ℝ => 1/(t^2 * Real.log t)) (Set.Icc n m) := by
    have hlog : ContinuousOn (fun t : ℝ => Real.log t) (Set.Icc n m) :=
      Real.continuousOn_log.mono (fun t ht => by
        simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
        have h1 : (1:ℝ) < t := lt_of_lt_of_le hn ht.1
        linarith)
    have hid : ContinuousOn (fun t : ℝ => t) (Set.Icc n m) := continuousOn_id
    exact continuousOn_const.div (hid.pow 2 |>.mul hlog) (fun t ht => by
      have h1 : (1:ℝ) < t := lt_of_lt_of_le hn ht.1
      have ht0 : t ≠ 0 := by linarith
      have hl0 : Real.log t ≠ 0 := ne_of_gt (Real.log_pos h1)
      exact mul_ne_zero (pow_ne_zero 2 ht0) hl0)
  have hPcont : ContinuousOn P (Set.Icc n m) := by
    rw [hP]
    have hlog : ContinuousOn (fun t : ℝ => Real.log t) (Set.Icc n m) :=
      Real.continuousOn_log.mono (fun t ht => by
        simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
        have h1 : (1:ℝ) < t := lt_of_lt_of_le hn ht.1
        linarith)
    have hid : ContinuousOn (fun t : ℝ => t) (Set.Icc n m) := continuousOn_id
    have htl : ContinuousOn (fun t : ℝ => t * Real.log t) (Set.Icc n m) := hid.mul hlog
    have hnum : ContinuousOn (fun t : ℝ => Real.log t + 1) (Set.Icc n m) :=
      hlog.add continuousOn_const
    have hne : ∀ t ∈ Set.Icc n m, (t * Real.log t)^2 ≠ 0 := by
      intro t ht
      have h1 : (1:ℝ) < t := lt_of_lt_of_le hn ht.1
      have ht0 : t ≠ 0 := by linarith
      have hl0 : Real.log t ≠ 0 := ne_of_gt (Real.log_pos h1)
      exact pow_ne_zero 2 (mul_ne_zero ht0 hl0)
    have h1 : ContinuousOn (fun t : ℝ => (Real.log t + 1)/(t * Real.log t)^2) (Set.Icc n m) :=
      hnum.div (htl.pow 2) hne
    have h2 : ContinuousOn (fun t : ℝ => ((Real.log n)^2)⁻¹ * (t^2)⁻¹) (Set.Icc n m) := by
      apply ContinuousOn.mul continuousOn_const
      apply ContinuousOn.inv₀ (hid.pow 2)
      intro t ht
      have h1 : (1:ℝ) < t := lt_of_lt_of_le hn ht.1
      have ht0 : t ≠ 0 := by linarith
      exact pow_ne_zero 2 ht0
    exact h1.sub h2
  have hFint : IntervalIntegrable (fun t : ℝ => 1/(t^2 * Real.log t)) volume n m :=
    hFcont.intervalIntegrable_of_Icc hnm
  have hPint : IntervalIntegrable P volume n m := hPcont.intervalIntegrable_of_Icc hnm
  -- pointwise comparison
  have hle : ∀ x ∈ Set.Icc n m, P x ≤ 1/(x^2 * Real.log x) := by
    intro x hx
    rw [hP]
    exact psi'_le_inv hn hx.1
  have hmono : ∫ t in n..m, P t ≤ ∫ t in n..m, 1/(t^2 * Real.log t) :=
    intervalIntegral.integral_mono_on hnm hPint hFint hle
  -- fundamental theorem of calculus
  have hderiv : ∀ x ∈ uIcc n m, HasDerivAt psi (P x) x := by
    intro x hx
    rw [uIcc_of_le hnm] at hx
    have hx1 : 1 < x := lt_of_lt_of_le hn hx.1
    show HasDerivAt (fun t => -((t * Real.log t)⁻¹) + ((Real.log n)^2)⁻¹ * t⁻¹)
      ((Real.log x + 1)/(x * Real.log x)^2 - ((Real.log n)^2)⁻¹ * (x^2)⁻¹) x
    exact psi_hasDerivAt hx1
  have hFTC : ∫ t in n..m, P t = psi m - psi n :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hPint
  have hkey : psi m - psi n ≤ ∫ t in n..m, 1/(t^2 * Real.log t) := by
    rw [← hFTC]; exact hmono
  -- bound on psi m - psi n
  have hpsi_bound : psi m - psi n
      ≥ (n * Real.log n)⁻¹ - (m * Real.log m)⁻¹ - (n * (Real.log n)^2)⁻¹ := by
    have hexp : psi m - psi n
        = (n * Real.log n)⁻¹ - (m * Real.log m)⁻¹ + ((Real.log n)^2)⁻¹ * (m⁻¹ - n⁻¹) := by
      rw [hpsi]; ring
    rw [hexp]
    have hc : 0 ≤ ((Real.log n)^2)⁻¹ := inv_nonneg.mpr (pow_nonneg (le_of_lt (Real.log_pos hn)) 2)
    have hterm : ((Real.log n)^2)⁻¹ * (m⁻¹ - n⁻¹) ≥ -(n * (Real.log n)^2)⁻¹ := by
      have hmn : -n⁻¹ ≤ m⁻¹ - n⁻¹ := by
        have : 0 ≤ m⁻¹ := inv_nonneg.mpr (by linarith)
        linarith
      calc -(n * (Real.log n)^2)⁻¹ = ((Real.log n)^2)⁻¹ * (-n⁻¹) := by rw [mul_inv]; ring
        _ ≤ ((Real.log n)^2)⁻¹ * (m⁻¹ - n⁻¹) := mul_le_mul_of_nonneg_left hmn hc
    linarith [hterm]
  -- reduce to the target expression
  have hMpos : 0 < min m (n^2) := lt_min (by linarith) (by positivity)
  have hMm0 : 0 < m * Real.log m := mul_pos (by linarith) (Real.log_pos (by linarith))
  have hMl0 : 0 < min m (n^2) * Real.log n := mul_pos hMpos (Real.log_pos hn)
  have hMlog : (m * Real.log m)⁻¹ ≤ (min m (n^2) * Real.log n)⁻¹ :=
    (inv_le_inv₀ hMm0 hMl0).mpr (by
      apply mul_le_mul
      · exact min_le_left m (n^2)
      · exact Real.log_le_log (by linarith) hnm
      · exact le_of_lt (Real.log_pos hn)
      · exact le_of_lt (by linarith))
  have htarget : (1/(n * Real.log n)) * (1 - n / min m (n^2) - 1/(Real.log n))
      = (n * Real.log n)⁻¹ - (min m (n^2) * Real.log n)⁻¹ - (n * (Real.log n)^2)⁻¹ := by
    have hM0 : min m (n^2) ≠ 0 := ne_of_gt hMpos
    field_simp
  rw [htarget]
  have step : (n * Real.log n)⁻¹ - (m * Real.log m)⁻¹ - (n * (Real.log n)^2)⁻¹
      ≥ (n * Real.log n)⁻¹ - (min m (n^2) * Real.log n)⁻¹ - (n * (Real.log n)^2)⁻¹ := by
    linarith [hMlog]
  linarith [hkey, hpsi_bound, step]

end Commons.Analysis.Real