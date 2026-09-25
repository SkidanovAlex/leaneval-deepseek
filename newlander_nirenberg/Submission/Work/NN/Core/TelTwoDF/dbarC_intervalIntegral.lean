import Mathlib
import Submission.Work.CR.Flat.Cauchy.dbarC_mul
import Submission.Work.CR.Flat.Cauchy.holderNorm_le_wirtinger

namespace Work.NN.Core.TelTwoDF

open MeasureTheory Set Filter

theorem dbarC_intervalIntegral {F : ℂ → ℝ → ℂ} {F' : ℂ → ℝ → ℂ →L[ℝ] ℂ} {w₀ : ℂ} {s : Set ℂ}
    {bound : ℝ → ℝ} {a b : ℝ} (hs : s ∈ nhds w₀) (hw₀ : w₀ ∈ s)
    (hF_meas : ∀ᶠ w in nhds w₀, MeasureTheory.AEStronglyMeasurable (F w) (MeasureTheory.volume.restrict (Set.uIoc a b)))
    (hF_int : IntervalIntegrable (F w₀) MeasureTheory.volume a b)
    (hF'_meas : MeasureTheory.AEStronglyMeasurable (F' w₀) (MeasureTheory.volume.restrict (Set.uIoc a b)))
    (h_bound : Filter.Eventually (fun t => t ∈ Set.uIoc a b → ∀ w ∈ s, ‖F' w t‖ ≤ bound t) (MeasureTheory.ae (MeasureTheory.volume : MeasureTheory.Measure ℝ)))
    (bound_int : IntervalIntegrable bound MeasureTheory.volume a b)
    (h_diff : Filter.Eventually (fun t => t ∈ Set.uIoc a b → ∀ w ∈ s,
      HasFDerivAt (fun w => F w t) (F' w t) w) (MeasureTheory.ae (MeasureTheory.volume : MeasureTheory.Measure ℝ))) :
    Work.CR.Flat.dbarC (fun w => ∫ t in a..b, F w t) w₀
      = ∫ t in a..b, Work.CR.Flat.dbarC (fun w => F w t) w₀ := by
  set L : ℂ →L[ℝ] ℂ := ∫ t in a..b, F' w₀ t with hL
  have hdbarC_pt : ∀ (u : ℂ → ℂ) (z : ℂ),
      Work.CR.Flat.dbarC u z = Work.CR.Flat.Cauchy.dbarCLM (fderiv ℝ u z) := by
    intro u z
    have h := congrFun (Work.CR.Flat.Cauchy.dbarC_eq_dbarCLM u) z
    simpa [Function.comp_apply] using h
  have hhas : HasFDerivAt (fun w => ∫ t in a..b, F w t) L w₀ := by
    rw [hL]
    refine intervalIntegral.hasFDerivAt_integral_of_dominated_of_fderiv_le
      (𝕜 := ℝ) (E := ℂ) (H := ℂ)
      (μ := (MeasureTheory.volume : MeasureTheory.Measure ℝ))
      (F := F) (F' := F') (x₀ := w₀) (s := s) (a := a) (b := b) (bound := bound)
      ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · exact hs
    · exact hF_meas
    · exact hF_int
    · exact hF'_meas
    · exact h_bound
    · exact bound_int
    · exact h_diff
  have hL_int : IntervalIntegrable (fun t => F' w₀ t) MeasureTheory.volume a b := by
    refine IntervalIntegrable.mono_fun' bound_int hF'_meas ?_
    rw [Filter.EventuallyLE, MeasureTheory.ae_restrict_iff' measurableSet_uIoc]
    filter_upwards [h_bound] with t ht hts
    exact ht hts w₀ hw₀
  have hcongr : ∀ᵐ t ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ),
      t ∈ Set.uIoc a b → Work.CR.Flat.dbarC (fun w => F w t) w₀
        = Work.CR.Flat.Cauchy.dbarCLM (F' w₀ t) := by
    filter_upwards [h_diff] with t ht hts
    rw [hdbarC_pt (fun w => F w t) w₀, (ht hts w₀ hw₀).fderiv]
  have step0 : Work.CR.Flat.dbarC (fun w => ∫ t in a..b, F w t) w₀
      = Work.CR.Flat.Cauchy.dbarCLM L := by
    rw [hdbarC_pt (fun w => ∫ t in a..b, F w t) w₀, hhas.fderiv]
  have step1 : ∫ t in a..b, Work.CR.Flat.dbarC (fun w => F w t) w₀
      = ∫ t in a..b, Work.CR.Flat.Cauchy.dbarCLM (F' w₀ t) :=
    intervalIntegral.integral_congr_ae hcongr
  have step2 : ∫ t in a..b, Work.CR.Flat.Cauchy.dbarCLM (F' w₀ t)
      = Work.CR.Flat.Cauchy.dbarCLM L := by
    rw [ContinuousLinearMap.intervalIntegral_comp_comm Work.CR.Flat.Cauchy.dbarCLM hL_int, hL]
  exact step0.trans ((step1.trans step2).symm)

end Work.NN.Core.TelTwoDF
