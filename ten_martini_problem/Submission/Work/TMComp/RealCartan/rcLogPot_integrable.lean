import Mathlib

open MeasureTheory Set

namespace Work.TMComp.RealCartan

/-- The logarithmic potential `t ↦ log (R / ‖z - t‖)` is integrable on any closed
interval `[a, b]`. The only possible singularity is a logarithmic one, which is
integrable; this is obtained from `MeromorphicOn.intervalIntegrable_log_norm`
applied to the affine (hence meromorphic) function `t ↦ z - t`. -/
theorem rcLogPot_integrable (z : ℂ) (R a b : ℝ) :
    MeasureTheory.IntegrableOn (fun t : ℝ => Real.log (R / ‖z - (t:ℂ)‖))
      (Set.Icc a b) MeasureTheory.volume := by
  -- Integrability of `log ‖z - t‖` from the meromorphic logarithm theorem.
  have hlog : IntervalIntegrable (fun t : ℝ => Real.log ‖z - (t:ℂ)‖) volume a b := by
    have hfun : (fun t : ℝ => (t:ℂ)) = (Complex.ofRealCLM : ℝ → ℂ) := by
      funext t; exact (Complex.ofRealCLM_apply t).symm
    have hc : AnalyticOnNhd ℝ (fun t : ℝ => (t:ℂ)) (uIcc a b) := by
      rw [hfun]; exact Complex.ofRealCLM.analyticOnNhd (uIcc a b)
    exact ((analyticOnNhd_const.sub hc).meromorphicOn).intervalIntegrable_log_norm
  -- The set where `‖z - t‖ = 0` is a subsingleton, hence has measure zero.
  have hbad : volume {t : ℝ | ‖z - (t:ℂ)‖ = 0} = 0 := by
    have hsub : {t : ℝ | ‖z - (t:ℂ)‖ = 0}.Subsingleton := by
      intro t1 ht1 t2 ht2
      simp only [Set.mem_ofPred_eq, norm_eq_zero, sub_eq_zero] at ht1 ht2
      apply Complex.ofReal_injective
      rw [← ht1, ht2]
    exact hsub.measure_zero volume
  by_cases hab : a ≤ b
  · rw [← intervalIntegrable_iff_integrableOn_Icc_of_le hab]
    by_cases hR : R = 0
    · -- `R = 0`: the function is identically zero.
      have hzero : (fun t : ℝ => Real.log (R / ‖z - (t:ℂ)‖)) = fun _ => 0 := by
        funext t; rw [hR, zero_div, Real.log_zero]
      rw [hzero]
      exact IntervalIntegrable.zero
    · -- `R ≠ 0`: off the singularity the function equals `log |R| - log ‖z - t‖`.
      have hneae : ∀ᵐ x : ℝ, ‖z - (x:ℂ)‖ ≠ 0 := by
        rw [MeasureTheory.ae_iff]; simpa using hbad
      have hae : (fun t : ℝ => Real.log |R| - Real.log ‖z - (t:ℂ)‖)
          =ᵐ[volume.restrict (Set.uIoc a b)]
          (fun t : ℝ => Real.log (R / ‖z - (t:ℂ)‖)) := by
        rw [Filter.EventuallyEq, MeasureTheory.ae_restrict_iff' measurableSet_uIoc]
        filter_upwards [hneae] with x hx _
        rw [Real.log_div hR hx, Real.log_abs]
      have hmain :
          IntervalIntegrable (fun t : ℝ => Real.log |R| - Real.log ‖z - (t:ℂ)‖) volume a b :=
        intervalIntegrable_const.sub hlog
      exact hmain.congr_ae hae
  · -- `a > b`: the interval is empty.
    rw [Set.Icc_eq_empty hab]
    exact integrableOn_empty

end Work.TMComp.RealCartan
