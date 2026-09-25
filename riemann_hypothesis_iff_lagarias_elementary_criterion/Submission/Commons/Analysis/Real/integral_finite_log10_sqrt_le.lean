import Mathlib
import Submission.Commons.Analysis.Real.tail_integral_log10
import Submission.Commons.Analysis.Real.integrableOn_log10_div_sqrt

noncomputable section

open Filter Set MeasureTheory
open scoped Interval Topology

namespace Commons.Analysis.Real

theorem integral_finite_log10_sqrt_le :
    ∃ K : ℝ, 0 < K ∧ ∀ x : ℝ, Real.exp 1 ≤ x → ∀ X : ℝ, x ≤ X →
      (∫ t in x..X, (Real.log t) ^ 10 / (t * Real.sqrt t)) ≤
        K * (Real.log x) ^ 10 / Real.sqrt x := by
  rcases tail_integral_log10 with ⟨K, hKpos, hK⟩
  refine ⟨K, hKpos, ?_⟩
  intro x hx X hxX
  have hcmp : (∫ t in x..X, (Real.log t) ^ 10 / (t * Real.sqrt t)) ≤
      (∫ t in Set.Ioi x, (Real.log t) ^ 10 / (t * Real.sqrt t)) := by
    rw [intervalIntegral.integral_of_le hxX]
    have h2x : (2 : ℝ) ≤ x := by
      exact le_of_lt (lt_of_lt_of_le Real.exp_one_gt_two hx)
    have hfi : IntegrableOn (fun t : ℝ => (Real.log t) ^ 10 / (t * Real.sqrt t))
        (Set.Ioi x) := integrableOn_log10_div_sqrt h2x
    have hf0 : 0 ≤ᵐ[volume.restrict (Set.Ioi x)]
        (fun t : ℝ => (Real.log t) ^ 10 / (t * Real.sqrt t)) := by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      have hxlt : x < t := ht
      have he : Real.exp 1 ≤ t := le_trans hx (le_of_lt hxlt)
      have hlog1 : 1 ≤ Real.log t := by
        have hlogle : Real.log (Real.exp 1) ≤ Real.log t :=
          Real.log_le_log (Real.exp_pos 1) he
        rwa [Real.log_exp] at hlogle
      have htpos : 0 < t := lt_of_lt_of_le (Real.exp_pos 1) he
      have hnum : 0 ≤ (Real.log t) ^ 10 := pow_nonneg (by linarith) 10
      have hden : 0 < t * Real.sqrt t := mul_pos htpos (Real.sqrt_pos.mpr htpos)
      exact div_nonneg hnum hden.le
    have hst : Set.Ioc x X ≤ᵐ[volume] Set.Ioi x := by
      refine ae_of_all _ ?_
      intro t ht
      exact Set.mem_Ioi.mpr (Set.mem_Ioc.mp ht).1
    exact MeasureTheory.setIntegral_mono_set (μ := volume) hfi hf0 hst
  exact le_trans hcmp (hK x hx)

end Commons.Analysis.Real
