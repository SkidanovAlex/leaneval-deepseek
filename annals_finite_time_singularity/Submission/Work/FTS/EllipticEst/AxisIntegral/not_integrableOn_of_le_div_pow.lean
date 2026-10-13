import Mathlib.Analysis.SpecialFunctions.Integrability.Basic

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.AxisIntegral

open MeasureTheory Set

/-- For `k ≥ 2` and `c > 0` the function `z ↦ c / z ^ k` is not integrable on `(0, ε)`:
the singularity at `0` is too strong.  (Compared with `Mathlib`'s
`intervalIntegral.integrableOn_Ioo_rpow_iff`, which gives integrability exactly for
`z ↦ z ^ s` with `-1 < s`.) -/
theorem not_integrableOn_const_div_pow {c ε : ℝ} {k : ℕ} (hc : 0 < c) (hε : 0 < ε)
    (hk : 2 ≤ k) :
    ¬ IntegrableOn (fun z : ℝ => c / z ^ k) (Ioo (0 : ℝ) ε) := by
  intro hg
  -- rewrite the integrand as `c * z ^ (-(k : ℝ))`
  have h1 : IntegrableOn (fun z : ℝ => c * z ^ (-(k : ℝ))) (Ioo (0 : ℝ) ε) := by
    refine hg.congr_fun (fun z hz => ?_) measurableSet_Ioo
    rw [Real.rpow_neg (le_of_lt hz.1) (k : ℝ), Real.rpow_natCast]
    ring
  -- divide by the non-zero constant `c`
  have h2 : IntegrableOn (fun z : ℝ => z ^ (-(k : ℝ))) (Ioo (0 : ℝ) ε) := by
    have h2' : Integrable (fun z : ℝ => z ^ (-(k : ℝ)))
        (volume.restrict (Ioo (0 : ℝ) ε)) := by
      have hfun : (fun z : ℝ => c⁻¹ * (c * z ^ (-(k : ℝ)))) =
          fun z : ℝ => z ^ (-(k : ℝ)) := by
        funext z
        rw [← mul_assoc, inv_mul_cancel₀ (ne_of_gt hc), one_mul]
      rw [← hfun]
      exact h1.integrable.const_mul c⁻¹
    exact h2'
  -- but `(-1) < -(k : ℝ)` is false for `k ≥ 2`
  have h4 := (intervalIntegral.integrableOn_Ioo_rpow_iff hε).mp h2
  have hk2 : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  linarith

theorem not_integrableOn_of_le_div_pow {f : ℝ → ℝ} {c ε : ℝ} {k : ℕ}
    (hc : 0 < c) (hε : 0 < ε) (hk : 2 ≤ k)
    (h : ∀ z ∈ Set.Ioo (0 : ℝ) ε, c / z ^ k ≤ f z) :
    ¬ MeasureTheory.IntegrableOn f (Set.Ioi (0 : ℝ)) := by
  intro hf
  -- restrict `f` to the small interval `(0, ε)`
  have hg : IntegrableOn (fun z : ℝ => c / z ^ k) (Ioo (0 : ℝ) ε) := by
    have hf' : IntegrableOn f (Ioo (0 : ℝ) ε) := hf.mono_set Ioo_subset_Ioi_self
    -- `c / z ^ k` is measurable and dominated by `f` on `(0, ε)`
    refine Integrable.mono' hf' ?_ ?_
    · exact Measurable.aestronglyMeasurable
        (Measurable.div measurable_const (Measurable.pow_const measurable_id k))
    · filter_upwards [ae_restrict_mem measurableSet_Ioo] with z hz
      rw [Real.norm_of_nonneg (div_nonneg hc.le (le_of_lt (pow_pos hz.1 k)))]
      exact h z hz
  exact not_integrableOn_const_div_pow hc hε hk hg

end Work.FTS.EllipticEst.AxisIntegral
