import Mathlib

namespace Work.TMComp.LocCantor

open MeasureTheory Set

/--
`log (max (f x) 0)` is interval integrable on `[0,1]` for a real-analytic function `f`
on a neighbourhood of `[0,1]`.

The key point is that `log ‖f ·‖` is interval integrable because `f` is meromorphic
(`MeromorphicOn.intervalIntegrable_log_norm`), while `log (max (f x) 0)` agrees with
`log ‖f x‖` when `f x > 0` and is `0` otherwise, hence is pointwise dominated by
`‖log ‖f x‖‖`.
-/
theorem integral_log_max_ge (f : ℝ → ℝ) (hf : AnalyticOnNhd ℝ f (Set.uIcc 0 1)) :
    IntervalIntegrable (fun x : ℝ => Real.log (max (f x) 0)) volume 0 1 := by
  -- `log ‖f ·‖` is interval integrable on `[0,1]`.
  have hlog : IntegrableOn (fun x : ℝ => Real.log ‖f x‖) (Set.Ioc 0 1) volume :=
    (hf.meromorphicOn.intervalIntegrable_log_norm).1
  have habs : IntegrableOn (fun x : ℝ => ‖Real.log ‖f x‖‖) (Set.Ioc 0 1) volume := hlog.norm
  -- Measurability of the target function on `(0,1]`.
  have hcont : ContinuousOn f (Set.uIcc 0 1) := hf.continuousOn
  have hsub : Set.Ioc (0 : ℝ) 1 ⊆ Set.uIcc 0 1 := by
    rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    exact Set.Ioc_subset_Icc_self
  have hae_f : AEMeasurable f (volume.restrict (Set.Ioc 0 1)) :=
    (hcont.mono hsub).aemeasurable measurableSet_Ioc
  have hae_max : AEMeasurable (fun x => max (f x) 0) (volume.restrict (Set.Ioc 0 1)) :=
    (continuous_id.max continuous_const).measurable.comp_aemeasurable hae_f
  have hae_log : AEMeasurable (fun x => Real.log (max (f x) 0))
      (volume.restrict (Set.Ioc 0 1)) :=
    Real.measurable_log.comp_aemeasurable hae_max
  have hmeas : AEStronglyMeasurable (fun x => Real.log (max (f x) 0))
      (volume.restrict (Set.Ioc 0 1)) :=
    hae_log.aestronglyMeasurable
  -- Pointwise domination by `‖log ‖f x‖‖`.
  have hbound : ∀ᵐ x ∂(volume.restrict (Set.Ioc 0 1)),
      ‖Real.log (max (f x) 0)‖ ≤ ‖Real.log ‖f x‖‖ := by
    apply Filter.Eventually.of_forall
    intro x
    rcases lt_or_ge 0 (f x) with h | h
    · rw [max_eq_left h.le, Real.norm_of_nonneg h.le]
    · rw [max_eq_right h]; simp
  have hint1 : Integrable (fun x => Real.log (max (f x) 0)) (volume.restrict (Set.Ioc 0 1)) :=
    Integrable.mono' habs hmeas hbound
  refine ⟨hint1, ?_⟩
  rw [show Set.Ioc 1 0 = (∅ : Set ℝ) by ext x; simp]
  exact integrableOn_empty

end Work.TMComp.LocCantor
