import Mathlib
import Submission.Work.LinnikAreas.A5.integral_exp_neg_sqrt_log_rpow_le
import Submission.Work.LinnikAreas.A5.integral_rpow_log_subst

open scoped Interval Topology BigOperators
open MeasureTheory

namespace Work.LinnikAreas.A5

/-- `∫_0^Y exp(-c√v) dv ≤ 2/c²` specialized form used with an explicit
antiderivative; here we bound the integral of `log q * exp(-c√(u log q))`
on `[0, x₀]` directly. -/
theorem integral_exp_neg_sqrt_rpow_le {x₀ R lam c : ℝ} (hx₀ : 0 < x₀) (hc : 0 < c)
    (hlam0 : 0 ≤ lam) (hlamR : lam ≤ R) {q : ℝ} (hq : 1 < q) :
    (∫ t in (1:ℝ)..q^x₀,
        Real.exp (-c * Real.sqrt (Real.log t)) * t ^ (-(1 - lam / Real.log q)))
      ≤ 2 * Real.exp (R * x₀) / c^2 := by
  have hq0 : (0:ℝ) < q := lt_trans zero_lt_one hq
  have hL : 0 < Real.log q := Real.log_pos hq
  have hR : 0 ≤ R := le_trans hlam0 hlamR
  have hb1 : (1:ℝ) ≤ q ^ x₀ := Real.one_le_rpow hq.le hx₀.le
  -- change of variables `t = q^u`, splitting off the `√(log t)` factor as `fr`
  set fr : ℝ → ℝ := fun u => Real.exp (-c * Real.sqrt (u * Real.log q)) with hfr
  have hfr_cont : Continuous fr := by rw [hfr]; fun_prop
  have hfrcont : ContinuousOn fr (Set.Icc (0:ℝ) x₀) := hfr_cont.continuousOn
  have hsub := integral_rpow_log_subst x₀ lam hx₀ hq (f := fr) hfrcont
  have hI1 : (∫ t in (1:ℝ)..q^x₀,
        Real.exp (-c * Real.sqrt (Real.log t)) * t ^ (-(1 - lam / Real.log q)))
      = ∫ t in (1:ℝ)..q^x₀, t ^ (-(1 - lam / Real.log q)) * fr (Real.log t / Real.log q) := by
    apply intervalIntegral.integral_congr
    intro t ht
    have htmem : t ∈ Set.Icc (1:ℝ) (q^x₀) := by rwa [Set.uIcc_of_le hb1] at ht
    have hLL : (Real.log t / Real.log q) * Real.log q = Real.log t := by
      rw [div_mul_cancel₀]; exact ne_of_gt hL
    simp only [hfr]
    rw [hLL]
    ring
  rw [hI1, hsub]
  -- explicit antiderivative of `u ↦ log q * exp (-c √(u log q))`
  set Ffun : ℝ → ℝ := fun u =>
    -(2 * Real.sqrt (u * Real.log q) / c + 2 / c^2) * Real.exp (-c * Real.sqrt (u * Real.log q)) with hFdef
  have hFcont : ContinuousOn Ffun (Set.Icc (0:ℝ) x₀) := by
    rw [hFdef]
    exact (by fun_prop : Continuous (fun u : ℝ =>
      -(2 * Real.sqrt (u * Real.log q) / c + 2 / c^2) * Real.exp (-c * Real.sqrt (u * Real.log q)))).continuousOn
  have hFderiv : ∀ u ∈ Set.Ioo (0:ℝ) x₀, HasDerivAt Ffun (Real.log q * fr u) u := by
    intro u hu
    have hu0 : 0 < u := hu.1
    simp only [hFdef, hfr]
    have hinner : HasDerivAt (fun u : ℝ => u * Real.log q) (Real.log q) u := by
      simpa using (hasDerivAt_id u).mul_const (Real.log q)
    have hSpos : 0 < Real.sqrt (u * Real.log q) := Real.sqrt_pos.mpr (mul_pos hu0 hL)
    have hsqu : HasDerivAt (fun u : ℝ => Real.sqrt (u * Real.log q)) (Real.log q / (2 * Real.sqrt (u * Real.log q))) u :=
      hinner.sqrt (ne_of_gt (mul_pos hu0 hL))
    have hA : HasDerivAt (fun w : ℝ => 2 * w / c + 2 / c^2) (2 / c) (Real.sqrt (u * Real.log q)) := by
      have h1 : HasDerivAt (fun w : ℝ => 2 * w / c) (2 / c) (Real.sqrt (u * Real.log q)) := by
        simpa using (((hasDerivAt_id (Real.sqrt (u * Real.log q))).const_mul 2).div_const c)
      exact h1.add_const (2 / c^2)
    have hB : HasDerivAt (fun w : ℝ => Real.exp (-c * w)) (Real.exp (-c * Real.sqrt (u * Real.log q)) * (-c)) (Real.sqrt (u * Real.log q)) := by
      have : HasDerivAt (fun w : ℝ => -c * w) (-c) (Real.sqrt (u * Real.log q)) := by
        simpa using (hasDerivAt_id (Real.sqrt (u * Real.log q))).const_mul (-c)
      simpa using this.exp
    have hnegA : HasDerivAt (fun w : ℝ => -(2 * w / c + 2 / c^2)) (-(2 / c)) (Real.sqrt (u * Real.log q)) := hA.neg
    have hg : HasDerivAt (fun w => -(2 * w / c + 2 / c^2) * Real.exp (-c * w))
        (2 * Real.sqrt (u * Real.log q) * Real.exp (-c * Real.sqrt (u * Real.log q))) (Real.sqrt (u * Real.log q)) := by
      have hprod := hnegA.mul hB
      have hval : -(2/c) * Real.exp (-c * Real.sqrt (u * Real.log q)) + (-(2 * Real.sqrt (u * Real.log q) / c + 2 / c^2)) * (Real.exp (-c * Real.sqrt (u * Real.log q)) * (-c)) = 2 * Real.sqrt (u * Real.log q) * Real.exp (-c * Real.sqrt (u * Real.log q)) := by
        have hcne : c ≠ 0 := ne_of_gt hc
        field_simp
        ring
      rw [hval] at hprod
      exact hprod
    have hcomp := hg.comp u hsqu
    have hval2 : (2 * Real.sqrt (u * Real.log q) * Real.exp (-c * Real.sqrt (u * Real.log q))) * (Real.log q / (2 * Real.sqrt (u * Real.log q))) = Real.log q * Real.exp (-c * Real.sqrt (u * Real.log q)) := by
      have hS : Real.sqrt (u * Real.log q) ≠ 0 := ne_of_gt hSpos
      field_simp
    rw [hval2] at hcomp
    exact hcomp
  have hint : IntervalIntegrable (fun u : ℝ => Real.log q * fr u) MeasureTheory.volume (0:ℝ) x₀ := by
    rw [hfr]
    exact (by fun_prop : Continuous (fun u : ℝ => Real.log q * Real.exp (-c * Real.sqrt (u * Real.log q)))).intervalIntegrable _ _
  have hfund := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hx₀.le hFcont hFderiv hint
  have hLfr : Real.log q * (∫ u in (0:ℝ)..x₀, fr u) = Ffun x₀ - Ffun 0 := by
    rw [← intervalIntegral.integral_const_mul]
    exact hfund
  have hF0 : Ffun 0 = -2/c^2 := by
    simp only [hFdef]
    rw [zero_mul, Real.sqrt_zero]
    simp only [mul_zero, Real.exp_zero, mul_one, zero_div, zero_add]
    ring
  have hmono : (∫ u in (0:ℝ)..x₀, Real.exp (lam * u) * fr u)
      ≤ ∫ u in (0:ℝ)..x₀, Real.exp (R * x₀) * fr u := by
    have hAcont : Continuous (fun u : ℝ => Real.exp (lam * u) * fr u) :=
      (Real.continuous_exp.comp (continuous_const.mul continuous_id)).mul hfr_cont
    have hBcont : Continuous (fun u : ℝ => Real.exp (R * x₀) * fr u) :=
      continuous_const.mul hfr_cont
    apply intervalIntegral.integral_mono_on hx₀.le
    · exact hAcont.intervalIntegrable _ _
    · exact hBcont.intervalIntegrable _ _
    · intro u hu
      have hu0 : 0 ≤ u := hu.1
      have hu1 : u ≤ x₀ := hu.2
      have hexp : Real.exp (lam * u) ≤ Real.exp (R * x₀) := by
        apply Real.exp_le_exp.mpr
        have h1 : lam * u ≤ R * u := mul_le_mul_of_nonneg_right hlamR hu0
        have h2 : R * u ≤ R * x₀ := mul_le_mul_of_nonneg_left hu1 hR
        linarith
      have hfrn : 0 ≤ fr u := by rw [hfr]; exact (Real.exp_pos _).le
      exact mul_le_mul_of_nonneg_right hexp hfrn
  have hstep2 : (∫ u in (0:ℝ)..x₀, Real.exp (R * x₀) * fr u) = Real.exp (R * x₀) * ∫ u in (0:ℝ)..x₀, fr u := by
    rw [intervalIntegral.integral_const_mul]
  have hFbound : Real.log q * (∫ u in (0:ℝ)..x₀, fr u) ≤ 2 / c^2 := by
    rw [hLfr]
    have hxle : Ffun x₀ ≤ 0 := by
      simp only [hFdef]
      apply mul_nonpos_of_nonpos_of_nonneg
      · apply neg_nonpos.mpr
        have : 0 ≤ Real.sqrt (x₀ * Real.log q) := Real.sqrt_nonneg _
        positivity
      · exact (Real.exp_pos _).le
    have hkey : Ffun x₀ - Ffun 0 = Ffun x₀ + 2/c^2 := by rw [hF0]; ring
    rw [hkey]
    linarith
  calc Real.log q * (∫ u in (0:ℝ)..x₀, Real.exp (lam * u) * fr u)
      ≤ Real.log q * (∫ u in (0:ℝ)..x₀, Real.exp (R * x₀) * fr u) :=
        mul_le_mul_of_nonneg_left hmono hL.le
    _ = Real.log q * (Real.exp (R * x₀) * ∫ u in (0:ℝ)..x₀, fr u) := by rw [hstep2]
    _ = Real.exp (R * x₀) * (Real.log q * ∫ u in (0:ℝ)..x₀, fr u) := by ring
    _ ≤ Real.exp (R * x₀) * (2 / c^2) := mul_le_mul_of_nonneg_left hFbound (Real.exp_pos _).le
    _ = 2 * Real.exp (R * x₀) / c^2 := by ring

end Work.LinnikAreas.A5
