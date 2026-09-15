import Mathlib
import Submission.Commons.Analysis.Fourier.fourierInv_toLp_ae_eq_fourierInv
import Submission.Commons.Analysis.Fourier.norm_sum_sq_le_of_bounded_overlap

namespace Commons.Analysis.Fourier

open MeasureTheory FourierTransform

set_option autoImplicit false

theorem integral_norm_sq_fourierInv_eq {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [MeasurableSpace V] [BorelSpace V] [FiniteDimensional ℝ V] {h : V → ℂ}
    (h1 : MeasureTheory.MemLp h 1 (MeasureTheory.volume : MeasureTheory.Measure V))
    (h2 : MeasureTheory.MemLp h 2 (MeasureTheory.volume : MeasureTheory.Measure V)) :
    ∫ x, ‖FourierTransform.fourierInv h x‖ ^ 2 = ∫ ξ, ‖h ξ‖ ^ 2 := by
  have hnorm :
      ‖(FourierTransform.fourierInv (h2.toLp h) :
          MeasureTheory.Lp ℂ 2 (MeasureTheory.volume : MeasureTheory.Measure V))‖
        = ‖h2.toLp h‖ :=
    (Lp.fourierTransformₗᵢ V ℂ).symm.norm_map (h2.toLp h)
  calc ∫ x, ‖FourierTransform.fourierInv h x‖ ^ 2
      = ∫ x, ‖((FourierTransform.fourierInv (h2.toLp h) :
            MeasureTheory.Lp ℂ 2 (MeasureTheory.volume : MeasureTheory.Measure V)) :
            V → ℂ) x‖ ^ 2 := by
          refine integral_congr_ae ?_
          filter_upwards [fourierInv_toLp_ae_eq_fourierInv h1 h2] with x hx
          rw [hx]
    _ = ‖(FourierTransform.fourierInv (h2.toLp h) :
            MeasureTheory.Lp ℂ 2 (MeasureTheory.volume : MeasureTheory.Measure V))‖ ^ 2 :=
          lp_integral_norm_sq _
    _ = ‖h2.toLp h‖ ^ 2 := by rw [hnorm]
    _ = ∫ x, ‖(h2.toLp h : V → ℂ) x‖ ^ 2 := (lp_integral_norm_sq _).symm
    _ = ∫ ξ, ‖h ξ‖ ^ 2 := by
          refine integral_congr_ae ?_
          filter_upwards [h2.coeFn_toLp] with x hx
          rw [hx]

end Commons.Analysis.Fourier
