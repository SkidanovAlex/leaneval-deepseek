import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Submission.Commons.Analysis.Real.poisson_hilbert_integrand_eq
import Submission.Commons.Analysis.Real.hasDerivAt_poisson_hilbert_antideriv
import Submission.Commons.Analysis.Real.tendsto_poisson_hilbert_antideriv

namespace Commons.Analysis.Real

open MeasureTheory Set Filter
open scoped Topology

theorem integral_poisson_hilbert_kernel {s y : ℝ} (hs : 0 < s) :
    ∫ t in Set.Ioi (0 : ℝ),
        ((1 / Real.pi) * (s / (s ^ 2 + (y - t) ^ 2))
          - (1 / Real.pi) * (s / (s ^ 2 + (y + t) ^ 2))) / t
      = y / (y ^ 2 + s ^ 2) := by
  set H : ℝ → ℝ := fun u : ℝ =>
        -(s / (2 * (y ^ 2 + s ^ 2))) *
            (Real.log ((u - y) ^ 2 + s ^ 2) - Real.log ((u + y) ^ 2 + s ^ 2))
          + (y / (y ^ 2 + s ^ 2)) *
            (Real.arctan ((u - y) / s) + Real.arctan ((u + y) / s)) with hH
  set g' : ℝ → ℝ := fun t : ℝ =>
        4 * s * y / (((t - y) ^ 2 + s ^ 2) * ((t + y) ^ 2 + s ^ 2)) with hg'
  have hderiv : ∀ x ∈ Set.Ici (0 : ℝ), HasDerivAt H (g' x) x := by
    intro x _
    simpa only [hH, hg'] using hasDerivAt_poisson_hilbert_antideriv hs x
  have hlim : Tendsto H atTop (𝓝 (Real.pi * y / (y ^ 2 + s ^ 2))) := by
    simpa only [hH] using tendsto_poisson_hilbert_antideriv hs
  have hH0 : H 0 = 0 := by
    simp only [hH]
    have h1 : ((0 : ℝ) - y) ^ 2 + s ^ 2 = ((0 : ℝ) + y) ^ 2 + s ^ 2 := by ring
    have h2 : ((0 : ℝ) - y) / s = -(((0 : ℝ) + y) / s) := by ring
    rw [h1, sub_self, h2, Real.arctan_neg]
    ring
  have hval : ∫ t in Set.Ioi (0 : ℝ), g' t = Real.pi * y / (y ^ 2 + s ^ 2) := by
    by_cases hy : 0 ≤ y
    · have hpos : ∀ x ∈ Set.Ioi (0 : ℝ), 0 ≤ g' x := by
        intro x _
        rw [hg']
        have hden : 0 < ((x - y) ^ 2 + s ^ 2) * ((x + y) ^ 2 + s ^ 2) := by
          have h1 : 0 < (x - y) ^ 2 + s ^ 2 := by nlinarith [sq_nonneg (x - y), pow_pos hs 2]
          have h2 : 0 < (x + y) ^ 2 + s ^ 2 := by nlinarith [sq_nonneg (x + y), pow_pos hs 2]
          exact mul_pos h1 h2
        exact div_nonneg (by nlinarith [hs, hy]) hden.le
      have h := integral_Ioi_of_hasDerivAt_of_nonneg' (a := (0 : ℝ)) hderiv hpos hlim
      rw [h, hH0, sub_zero]
    · have hy0 : y < 0 := lt_of_not_ge hy
      have hneg : ∀ x ∈ Set.Ioi (0 : ℝ), g' x ≤ 0 := by
        intro x _
        rw [hg']
        have hden : 0 < ((x - y) ^ 2 + s ^ 2) * ((x + y) ^ 2 + s ^ 2) := by
          have h1 : 0 < (x - y) ^ 2 + s ^ 2 := by nlinarith [sq_nonneg (x - y), pow_pos hs 2]
          have h2 : 0 < (x + y) ^ 2 + s ^ 2 := by nlinarith [sq_nonneg (x + y), pow_pos hs 2]
          exact mul_pos h1 h2
        exact div_nonpos_of_nonpos_of_nonneg (by nlinarith [hs, hy0]) hden.le
      have h := integral_Ioi_of_hasDerivAt_of_nonpos' (a := (0 : ℝ)) hderiv hneg hlim
      rw [h, hH0, sub_zero]
  have hcongr : (∫ t in Set.Ioi (0 : ℝ),
        ((1 / Real.pi) * (s / (s ^ 2 + (y - t) ^ 2))
          - (1 / Real.pi) * (s / (s ^ 2 + (y + t) ^ 2))) / t)
      = ∫ t in Set.Ioi (0 : ℝ), (1 / Real.pi) * g' t := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro t ht
    have ht0 : t ≠ 0 := ne_of_gt ht
    simp only []
    rw [poisson_hilbert_integrand_eq hs ht0]
    simp only [hg']
    ring_nf
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  have hcne : y ^ 2 + s ^ 2 ≠ 0 := by positivity
  calc (∫ t in Set.Ioi (0 : ℝ),
        ((1 / Real.pi) * (s / (s ^ 2 + (y - t) ^ 2))
          - (1 / Real.pi) * (s / (s ^ 2 + (y + t) ^ 2))) / t)
      = ∫ t in Set.Ioi (0 : ℝ), (1 / Real.pi) * g' t := hcongr
    _ = (1 / Real.pi) * ∫ t in Set.Ioi (0 : ℝ), g' t := by
          rw [MeasureTheory.integral_const_mul]
    _ = (1 / Real.pi) * (Real.pi * y / (y ^ 2 + s ^ 2)) := by rw [hval]
    _ = y / (y ^ 2 + s ^ 2) := by field_simp

end Commons.Analysis.Real