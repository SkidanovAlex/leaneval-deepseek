import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Submission.Commons.MeasureTheory.IntervalIntegral.integral_subinterval_le

open MeasureTheory Set
open scoped Interval

namespace Commons.MeasureTheory.Integral

/-- **Coverage inequality for interval integrals.**  For a nonnegative continuous `f`,
`∫_{1/2}^2 f(s) ds ≤ 2 ∫_{1/2}^2 ∫_{1/2}^2 f(s t) ds dt`.

The point is that for each `t ∈ [1/2,2]` the substitution `u = s t` turns the inner integral
into `t⁻¹ ∫_{t/2}^{2t} f(u) du`, and every `u ∈ [1/2,2]` is covered by `{t : t/2 ≤ u ≤ 2t}`
with total `∫ dt/t ≥ log 2`.  Consequently the double integral dominates the single one up to
the universal factor `1/log 2 < 2`.  This is the "dyadic doubling" step used in §4 of Cohen's
fractal uncertainty paper. -/
theorem intervalIntegral_le_two_mul_double (f : ℝ → ℝ) (hcont : Continuous f)
    (hnn : ∀ x, 0 ≤ f x) :
    ∫ s in (1 / 2 : ℝ)..2, f s
      ≤ 2 * ∫ t in (1 / 2 : ℝ)..2, ∫ s in (1 / 2 : ℝ)..2, f (s * t) := by
  set h : ℝ → ℝ := fun t => ∫ s in (1 / 2 : ℝ)..2, f (s * t) with hh
  have hcont_h : Continuous h := by
    rw [hh]; fun_prop
  set A1 : ℝ := ∫ s in (1 / 2 : ℝ)..1, f s with hA1
  set A2 : ℝ := ∫ s in (1 : ℝ)..2, f s with hA2
  have hLsplit : (∫ s in (1 / 2 : ℝ)..2, f s) = A1 + A2 := by
    rw [hA1, hA2]
    exact (intervalIntegral.integral_add_adjacent_intervals
      (hcont.intervalIntegrable _ _) (hcont.intervalIntegrable _ _)).symm
  have hDsplit : (∫ t in (1 / 2 : ℝ)..2, h t)
      = (∫ t in (1 / 2 : ℝ)..1, h t) + ∫ t in (1 : ℝ)..2, h t :=
    (intervalIntegral.integral_add_adjacent_intervals
      (hcont_h.intervalIntegrable _ _) (hcont_h.intervalIntegrable _ _)).symm
  -- pointwise lower bounds
  have P1 : (1 / 2 : ℝ) * A1 ≤ ∫ t in (1 / 2 : ℝ)..1, h t := by
    have hpt : ∀ t ∈ Icc (1 / 2 : ℝ) 1, (fun _ : ℝ => A1) t ≤ h t := by
      intro t ht
      have ht1 : (1 / 2 : ℝ) ≤ t := ht.1
      have ht2 : t ≤ 1 := ht.2
      have ht0 : t ≠ 0 := by linarith
      show A1 ≤ h t
      simp only [hh]
      rw [intervalIntegral.integral_comp_mul_right f ht0]
      simp only [smul_eq_mul]
      rw [show (1 / 2 : ℝ) * t = t / 2 by ring]
      have hlow : A1 ≤ ∫ x in t / 2..2 * t, f x :=
        Commons.MeasureTheory.IntervalIntegral.integral_subinterval_le
          (a := (1 / 2 : ℝ)) (b := 1) (c := t / 2) (d := 2 * t)
          (by linarith) (by norm_num) (by linarith)
          (hcont.intervalIntegrable _ _) hnn
      have hA : 0 ≤ ∫ x in t / 2..2 * t, f x :=
        intervalIntegral.integral_nonneg_of_forall (by linarith) hnn
      have htinv : 1 ≤ t⁻¹ := by
        rw [one_le_inv₀ (by linarith)]; exact ht2
      calc A1 ≤ ∫ x in t / 2..2 * t, f x := hlow
        _ = 1 * ∫ x in t / 2..2 * t, f x := (one_mul _).symm
        _ ≤ t⁻¹ * ∫ x in t / 2..2 * t, f x := mul_le_mul_of_nonneg_right htinv hA
    have := intervalIntegral.integral_mono_on (μ := volume) (a := (1 / 2 : ℝ)) (b := 1)
      (by norm_num) (continuous_const.intervalIntegrable _ _)
      (hcont_h.intervalIntegrable _ _) hpt
    have hc : (∫ u in (1 / 2 : ℝ)..1, (fun _ : ℝ => A1) u) = (1 / 2) * A1 := by
      rw [intervalIntegral.integral_const, smul_eq_mul]; ring
    rwa [hc] at this
  have P2 : (1 / 2 : ℝ) * A2 ≤ ∫ t in (1 : ℝ)..2, h t := by
    have hpt : ∀ t ∈ Icc (1 : ℝ) 2, (fun _ : ℝ => (1 / 2) * A2) t ≤ h t := by
      intro t ht
      have ht1 : (1 : ℝ) ≤ t := ht.1
      have ht2 : t ≤ 2 := ht.2
      have ht0 : t ≠ 0 := by linarith
      show (1 / 2) * A2 ≤ h t
      simp only [hh]
      rw [intervalIntegral.integral_comp_mul_right f ht0]
      simp only [smul_eq_mul]
      rw [show (1 / 2 : ℝ) * t = t / 2 by ring]
      have hlow : A2 ≤ ∫ x in t / 2..2 * t, f x :=
        Commons.MeasureTheory.IntervalIntegral.integral_subinterval_le
          (a := (1 : ℝ)) (b := 2) (c := t / 2) (d := 2 * t)
          (by linarith) (by norm_num) (by linarith)
          (hcont.intervalIntegrable _ _) hnn
      have hA : 0 ≤ ∫ x in t / 2..2 * t, f x :=
        intervalIntegral.integral_nonneg_of_forall (by linarith) hnn
      have htinv : (1 / 2 : ℝ) ≤ t⁻¹ := by
        simpa using one_div_le_one_div_of_le (show (0:ℝ) < t by linarith) ht2
      calc (1 / 2) * A2 ≤ (1 / 2) * ∫ x in t / 2..2 * t, f x :=
            mul_le_mul_of_nonneg_left hlow (by norm_num)
        _ ≤ t⁻¹ * ∫ x in t / 2..2 * t, f x := mul_le_mul_of_nonneg_right htinv hA
    have := intervalIntegral.integral_mono_on (μ := volume) (a := (1 : ℝ)) (b := 2)
      (by norm_num) (continuous_const.intervalIntegrable _ _)
      (hcont_h.intervalIntegrable _ _) hpt
    have hc : (∫ u in (1 : ℝ)..2, (fun _ : ℝ => (1 / 2) * A2) u) = (1 / 2) * A2 := by
      rw [intervalIntegral.integral_const, smul_eq_mul]; ring
    rwa [hc] at this
  have hhalf : (1 / 2 : ℝ) * (A1 + A2)
      ≤ (∫ t in (1 / 2 : ℝ)..1, h t) + ∫ t in (1 : ℝ)..2, h t := by
    linarith [P1, P2]
  have hmain : (1 / 2 : ℝ) * (∫ s in (1 / 2 : ℝ)..2, f s) ≤ ∫ t in (1 / 2 : ℝ)..2, h t := by
    rw [hDsplit, hLsplit]
    exact hhalf
  linarith [hmain]

end Commons.MeasureTheory.Integral