import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.MeasureTheory.Function.LpSpace.InfiniteSum
import Mathlib.Topology.Separation.CompletelyRegular
import Submission.Commons.MeasureTheory.Integral.integrable_tsum_of_nonneg

open MeasureTheory
open scoped ENNReal NNReal

namespace Commons.MeasureTheory

theorem integrable_tsum_of_summable_integral_norm {α ι : Type*} [MeasurableSpace α]
    {μ : MeasureTheory.Measure α} [Countable ι] {F : ι → α → ℂ}
    (hF : ∀ i, MeasureTheory.Integrable (F i) μ)
    (hsum : Summable fun i => ∫ a, ‖F i a‖ ∂μ) :
    MeasureTheory.Integrable (fun a => ∑' i, F i a) μ := by
  have hF_meas : ∀ i, AEStronglyMeasurable (F i) μ := fun i => (hF i).1
  -- The series of L¹ norms is finite.
  have hE : (∑' i, ∫⁻ a, ‖F i a‖ₑ ∂μ) ≠ ⊤ := by
    have hcongr : ∀ i, (∫⁻ a, ‖F i a‖ₑ ∂μ) = ENNReal.ofReal (∫ a, ‖F i a‖ ∂μ) :=
      fun i => (ofReal_integral_norm_eq_lintegral_enorm (hF i)).symm
    rw [tsum_congr hcongr]
    rw [← ENNReal.ofReal_tsum_of_nonneg
      (fun i => integral_nonneg fun a => norm_nonneg (F i a)) hsum]
    exact ENNReal.ofReal_ne_top
  -- Hence the norms are a.e. pointwise summable.
  have hsum_norm : ∀ᵐ a ∂μ, Summable fun i => ‖F i a‖ := by
    refine summable_norm_of_tsum_eLpNorm_ne_top le_rfl hF_meas ?_
    simpa only [eLpNorm_one_eq_lintegral_enorm] using hE
  -- The (nonnegative, real-valued) series of norms is integrable.
  have hint_norm : Integrable (fun a => ∑' i, ‖F i a‖) μ :=
    (Integral.integrable_tsum_of_nonneg (f := fun i a => ‖F i a‖)
      (fun i => (hF_meas i).norm)
      (fun i a => norm_nonneg (F i a))
      (by
        have hcongr : ∀ i, (∫⁻ a, ENNReal.ofReal ‖F i a‖ ∂μ) = ∫⁻ a, ‖F i a‖ₑ ∂μ :=
          fun i => lintegral_congr fun a => ofReal_norm (F i a)
        rw [tsum_congr hcongr]
        rw [tsum_congr (fun i => (ofReal_integral_norm_eq_lintegral_enorm (hF i)).symm)]
        rw [← ENNReal.ofReal_tsum_of_nonneg
          (fun i => integral_nonneg fun a => norm_nonneg (F i a)) hsum]
        exact ENNReal.ofReal_ne_top)).1
  refine Integrable.mono' hint_norm (AEStronglyMeasurable.tsum hF_meas) ?_
  filter_upwards [hsum_norm] with a ha
  exact norm_tsum_le_tsum_norm ha

end Commons.MeasureTheory