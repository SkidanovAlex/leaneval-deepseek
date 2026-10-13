import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.EllExist.Honesty.radGreen_psiEnvelope

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PhiStar.Honesty

open MeasureTheory Set

/-- Tonelli/Fubini for the triangular region `1 < z < t` in `ℝ × ℝ`, in the form in which the
`PhiStar` tail estimates need it: the iterated `lintegral` over `(1,∞) × (z,∞)` equals the
iterated `lintegral` over the region `{(z,t) | 1 < z ∧ z < t}`, integrated first in `z`.
Both integrands are the product `P z * Q t`; the hypothesis `P z ≠ ⊤` (resp. `Q t ≠ ⊤`)
is what allows the (possibly non-measurable) factor to be pulled out of the inner integral. -/
theorem lintegral_tail_swap_Ioi_one {P Q : ℝ → ENNReal}
    (hP : AEMeasurable P (MeasureTheory.volume.restrict (Set.Ioi (1 : ℝ))))
    (hQ : AEMeasurable Q (MeasureTheory.volume.restrict (Set.Ioi (1 : ℝ))))
    (hPtop : ∀ z, P z ≠ ⊤) (hQtop : ∀ t, Q t ≠ ⊤) :
    ∫⁻ z in Set.Ioi (1 : ℝ), P z * (∫⁻ t in Set.Ioi z, Q t)
      = ∫⁻ t in Set.Ioi (1 : ℝ), Q t * (∫⁻ z in (Set.Ioi (1 : ℝ) ∩ Set.Iio t), P z) := by
  let f : ℝ → ℝ → ENNReal := fun z t => P z * (Set.Ioi z).indicator Q t
  -- `f` is a.e. measurable for the product of the restricted measures
  have hmeas : AEMeasurable (Function.uncurry f)
      ((MeasureTheory.volume.restrict (Set.Ioi (1 : ℝ))).prod
       (MeasureTheory.volume.restrict (Set.Ioi (1 : ℝ)))) := by
    have hfun : Function.uncurry f
        = fun p : ℝ × ℝ =>
            P p.1 * (Set.indicator {q : ℝ × ℝ | q.1 < q.2} (fun q => Q q.2)) p := by
      funext p
      by_cases h : p.1 < p.2 <;>
        simp [Function.uncurry, f, Set.indicator_of_mem, Set.indicator_of_notMem,
          Set.mem_Ioi, h]
    rw [hfun]
    exact (AEMeasurable.comp_fst hP).mul
      ((AEMeasurable.comp_snd hQ).indicator (measurableSet_lt measurable_fst measurable_snd))
  have hswap := lintegral_lintegral_swap (μ := MeasureTheory.volume.restrict (Set.Ioi (1 : ℝ)))
    (ν := MeasureTheory.volume.restrict (Set.Ioi (1 : ℝ))) (f := f) hmeas
  calc ∫⁻ z in Set.Ioi (1 : ℝ), P z * (∫⁻ t in Set.Ioi z, Q t)
      = ∫⁻ z in Set.Ioi (1 : ℝ),
          (∫⁻ t, f z t ∂(MeasureTheory.volume.restrict (Set.Ioi (1 : ℝ)))) := by
        -- for `z ∈ (1,∞)`: pull `P z` out of the `t`-integral
        apply setLIntegral_congr_fun measurableSet_Ioi
        intro z hz
        have hsub : Set.Ioi z ⊆ Set.Ioi (1 : ℝ) :=
          fun y hy => Set.mem_Ioi.mpr (lt_trans hz (Set.mem_Ioi.mp hy))
        calc P z * (∫⁻ t in Set.Ioi z, Q t)
            = P z * (∫⁻ t in Set.Ioi z, Q t
                ∂(MeasureTheory.volume.restrict (Set.Ioi (1 : ℝ)))) := by
              rw [Measure.restrict_restrict_of_subset hsub]
          _ = P z * ∫⁻ t, (Set.Ioi z).indicator Q t
                ∂(MeasureTheory.volume.restrict (Set.Ioi (1 : ℝ))) := by
              rw [lintegral_indicator measurableSet_Ioi]
          _ = ∫⁻ t, P z * (Set.Ioi z).indicator Q t
                ∂(MeasureTheory.volume.restrict (Set.Ioi (1 : ℝ))) :=
              (lintegral_const_mul' (P z) (fun t => (Set.Ioi z).indicator Q t) (hPtop z)).symm
          _ = ∫⁻ t, f z t ∂(MeasureTheory.volume.restrict (Set.Ioi (1 : ℝ))) := rfl
    _ = ∫⁻ z, (∫⁻ t, f z t ∂(MeasureTheory.volume.restrict (Set.Ioi (1 : ℝ))))
            ∂(MeasureTheory.volume.restrict (Set.Ioi (1 : ℝ))) := rfl
    _ = ∫⁻ t, (∫⁻ z, f z t ∂(MeasureTheory.volume.restrict (Set.Ioi (1 : ℝ))))
            ∂(MeasureTheory.volume.restrict (Set.Ioi (1 : ℝ))) := hswap
    _ = ∫⁻ t in Set.Ioi (1 : ℝ),
          (∫⁻ z, f z t ∂(MeasureTheory.volume.restrict (Set.Ioi (1 : ℝ)))) := rfl
    _ = ∫⁻ t in Set.Ioi (1 : ℝ), Q t * (∫⁻ z in (Set.Ioi (1 : ℝ) ∩ Set.Iio t), P z) := by
        -- for `t ∈ (1,∞)`: pull `Q t` out of the `z`-integral
        apply setLIntegral_congr_fun measurableSet_Ioi
        intro t ht
        calc ∫⁻ z, f z t ∂(MeasureTheory.volume.restrict (Set.Ioi (1 : ℝ)))
            = ∫⁻ z in Set.Ioi (1 : ℝ), f z t ∂MeasureTheory.volume := rfl
          _ = ∫⁻ z in Set.Ioi (1 : ℝ), (Set.Iio t).indicator P z * Q t
                ∂MeasureTheory.volume := by
              apply setLIntegral_congr_fun measurableSet_Ioi
              intro z hz
              by_cases h : z < t <;>
                simp [f, Set.indicator_of_mem, Set.indicator_of_notMem, Set.mem_Ioi,
                  Set.mem_Iio, h]
          _ = (∫⁻ z in Set.Ioi (1 : ℝ), (Set.Iio t).indicator P z ∂MeasureTheory.volume) * Q t :=
              lintegral_mul_const' (Q t) (fun z => (Set.Iio t).indicator P z) (hQtop t)
          _ = (∫⁻ z in (Set.Iio t ∩ Set.Ioi (1 : ℝ)), P z ∂MeasureTheory.volume) * Q t := by
              rw [setLIntegral_indicator measurableSet_Iio P]
          _ = Q t * (∫⁻ z in (Set.Ioi (1 : ℝ) ∩ Set.Iio t), P z ∂MeasureTheory.volume) := by
              rw [Set.inter_comm (Set.Iio t) (Set.Ioi (1 : ℝ))]
              exact mul_comm _ _

end Work.FTS.PhiStar.Honesty
