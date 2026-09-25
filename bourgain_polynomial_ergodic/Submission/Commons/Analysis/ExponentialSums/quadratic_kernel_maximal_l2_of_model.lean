import Mathlib
import Submission.Commons.Analysis.ExponentialSums.quadratic_kernel_dyadic_of_model
import Submission.Commons.Analysis.ExponentialSums.quadratic_kernel_dyadic_reduction_z
import Submission.Commons.Analysis.ExponentialSums.quadratic_kernel_shift_transfer

namespace Commons.Analysis.ExponentialSums

open MeasureTheory Filter Finset
open scoped BigOperators ENNReal Topology

theorem quadratic_kernel_maximal_l2_of_model
    (hmodel : ∃ A : ℝ, 0 < A ∧ ∀ (g : ℤ → ℂ) (s : Finset ℤ), (∀ n, n ∉ s → g n = 0) →
      ∫⁻ m : ℤ, (⨆ k : ℕ, ‖∫ θ in (0:ℝ)..1,
            (starRingEnd ℂ (Commons.Analysis.ExponentialSums.majorArcModel ((1:ℝ)/4) (2^k) θ)) *
            (∑ j ∈ s, g j * Complex.exp (2 * Real.pi * Complex.I * (j:ℂ) * (θ:ℂ))) *
            Complex.exp (-(2 * Real.pi * Complex.I * (m:ℂ) * (θ:ℂ)))‖ₑ) ^ (2:ℝ)
          ∂MeasureTheory.Measure.count
        ≤ ENNReal.ofReal (A ^ 2) * ∫⁻ m : ℤ, ‖g m‖ₑ ^ (2:ℝ) ∂MeasureTheory.Measure.count) :
    ∃ C : ℝ, 0 < C ∧ ∀ g : ℕ → ℝ, (∃ s : Finset ℕ, ∀ n, n ∉ s → g n = 0) →
      ∫⁻ m, (⨆ N : ℕ, ‖(N : ℝ)⁻¹ * ∑ i ∈ Finset.range N, g (m + i ^ 2)‖ₑ) ^ (2 : ℝ)
          ∂MeasureTheory.Measure.count
        ≤ ENNReal.ofReal (C ^ 2) * ∫⁻ m, ‖g m‖ₑ ^ (2 : ℝ) ∂MeasureTheory.Measure.count :=
  quadratic_kernel_shift_transfer
    (quadratic_kernel_dyadic_reduction_z (quadratic_kernel_dyadic_of_model hmodel))

end Commons.Analysis.ExponentialSums
