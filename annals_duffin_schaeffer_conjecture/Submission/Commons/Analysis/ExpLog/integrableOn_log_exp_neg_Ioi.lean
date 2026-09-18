import Mathlib.Analysis.SpecialFunctions.Gamma.Basic

open Filter Asymptotics Set MeasureTheory

namespace Commons.Analysis.ExpLog

lemma integrableOn_log_exp_neg_Ioi (c : ℝ) (hc : 0 < c) :
    MeasureTheory.IntegrableOn (fun u : ℝ => Real.log u * Real.exp (-u)) (Set.Ioi c)
      MeasureTheory.volume := by
  -- (a) continuity of u ↦ log u * exp (-u) on Ici c
  have hcont : ContinuousOn (fun u : ℝ => Real.log u * Real.exp (-u)) (Set.Ici c) := by
    have hlog : ContinuousOn (fun u : ℝ => Real.log u) (Set.Ici c) := by
      refine Real.continuousOn_log.mono ?_
      intro u hu
      exact Set.mem_compl_singleton_iff.mpr (ne_of_gt (lt_of_lt_of_le hc hu))
    have hexp : ContinuousOn (fun u : ℝ => Real.exp (-u)) (Set.Ici c) := by
      exact (Real.continuous_exp.comp (continuous_neg : Continuous fun u : ℝ => -u)).continuousOn
    exact hlog.mul hexp
  -- (b) u * exp (-u) is o (exp (-(1/2) * u)) at ∞  (Gamma-type asymptotic)
  have hfun : (fun u : ℝ => Real.exp (-u) * u ^ (1 : ℝ)) = fun u : ℝ => u * Real.exp (-u) := by
    funext u
    rw [Real.rpow_one]
    ring
  have hg : (fun u : ℝ => u * Real.exp (-u)) =o[atTop]
      (fun u : ℝ => Real.exp (-(1 / 2 : ℝ) * u)) := by
    have hGamma : (fun u : ℝ => Real.exp (-u) * u ^ (1 : ℝ)) =o[atTop]
        (fun u : ℝ => Real.exp (-(1 / 2 : ℝ) * u)) := Real.Gamma_integrand_isLittleO (1 : ℝ)
    simpa [← hfun] using hGamma
  -- (c) log u * exp (-u) =O u * exp (-u) at ∞  (since log u ≤ u for u ≥ 1)
  have hO1 : (fun u : ℝ => Real.log u * Real.exp (-u)) =O[atTop]
      (fun u : ℝ => u * Real.exp (-u)) := by
    refine Asymptotics.IsBigO.of_bound 1 ?_
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with u hu
    have hu0 : 0 ≤ u := by linarith
    have hlog_nonneg : 0 ≤ Real.log u := Real.log_nonneg hu
    have hlog_le : Real.log u ≤ u := Real.log_le_self hu0
    have hep_nonneg : 0 ≤ Real.exp (-u) := Real.exp_nonneg (-u)
    calc
      ‖Real.log u * Real.exp (-u)‖ = Real.log u * Real.exp (-u) := by
        rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hlog_nonneg, abs_of_nonneg hep_nonneg]
      _ ≤ u * Real.exp (-u) := mul_le_mul_of_nonneg_right hlog_le hep_nonneg
      _ = 1 * ‖u * Real.exp (-u)‖ := by
        rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hu0, abs_of_nonneg hep_nonneg]
        ring
  have hO : (fun u : ℝ => Real.log u * Real.exp (-u)) =O[atTop]
      (fun u : ℝ => Real.exp (-(1 / 2 : ℝ) * u)) := hO1.trans hg.isBigO
  -- assemble
  exact integrable_of_isBigO_exp_neg (a := c) (b := (1 / 2 : ℝ)) (by norm_num) hcont hO

end Commons.Analysis.ExpLog