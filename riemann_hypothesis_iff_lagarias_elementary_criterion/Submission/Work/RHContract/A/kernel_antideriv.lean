import Mathlib
import Submission.Work.RHContract.Corpus

/-!
# The antiderivative of the kernel `kW`

For `t > 1`,

`G(t) = -1/(t log t)`  satisfies  `G'(t) = k(t) = (log t + 1)/(t² log²t)`,

because `(d/dt)(t log t) = log t + 1`, so `G' = (log t + 1)/(t log t)² = k(t)`.
Consequently `k` is integrable on `(x, ∞)` for `x > 1`.
-/

namespace Work.RHContract.A

/-- `G(t) = -1/(t log t)` has derivative `k(t) = kW t` for `t > 1`. -/
lemma kW_hasDerivAt_antideriv {t : ℝ} (ht : 1 < t) :
    HasDerivAt (fun s : ℝ => -1 / (s * Real.log s)) (Work.RHContract.kW t) t := by
  have ht0 : t ≠ 0 := by linarith
  have hlog : Real.log t ≠ 0 := ne_of_gt (Real.log_pos ht)
  have h1 : HasDerivAt (fun s : ℝ => s) 1 t := by simpa using hasDerivAt_pow 1 t
  have hden : HasDerivAt (fun s : ℝ => s * Real.log s) (1 * Real.log t + t * t⁻¹) t :=
    h1.mul (Real.hasDerivAt_log ht0)
  have hden_ne : (fun s : ℝ => s * Real.log s) t ≠ 0 := by
    simp only; exact mul_ne_zero ht0 hlog
  have hnum : HasDerivAt (fun _ : ℝ => (-1:ℝ)) 0 t := hasDerivAt_const t (-1)
  have h := hnum.div hden hden_ne
  convert h using 1 <;> try rfl
  change (Real.log t + 1) / (t ^ 2 * (Real.log t) ^ 2)
       = (0 * (t * Real.log t) - -1 * (1 * Real.log t + t * t⁻¹)) / (t * Real.log t) ^ 2
  field_simp
  ring

/-- `1/(t log t) → 0` as `t → ∞`. -/
lemma one_div_mul_log_tendsto :
    Filter.Tendsto (fun s : ℝ => 1 / (s * Real.log s)) Filter.atTop (nhds 0) := by
  refine squeeze_zero' (g := fun s : ℝ => 1 / s) ?_ ?_ ?_
  · filter_upwards [Filter.eventually_gt_atTop (1:ℝ)] with s hs
    have hs0 : (0:ℝ) < s := by linarith
    have hl : 0 < Real.log s := Real.log_pos hs
    positivity
  · filter_upwards [Filter.eventually_gt_atTop (1:ℝ),
      Real.tendsto_log_atTop.eventually (Filter.eventually_ge_atTop (1:ℝ))] with s hs hlog
    have hs0 : (0:ℝ) < s := by linarith
    exact one_div_le_one_div_of_le hs0 (le_mul_of_one_le_right (le_of_lt hs0) hlog)
  · simpa [one_div] using
      (tendsto_inv_atTop_zero : Filter.Tendsto (fun s : ℝ => s⁻¹) Filter.atTop (nhds 0))

/-- `G(t) = -1/(t log t) → 0` as `t → ∞`. -/
lemma kW_antideriv_tendsto :
    Filter.Tendsto (fun s : ℝ => -1 / (s * Real.log s)) Filter.atTop (nhds 0) := by
  have h := one_div_mul_log_tendsto.neg
  simpa [neg_div] using h

/-- The kernel `kW` is integrable on `(x, ∞)` for `x > 1`. -/
lemma integrableOn_kW (x : ℝ) (hx : 1 < x) :
    MeasureTheory.IntegrableOn Work.RHContract.kW (Set.Ioi x) := by
  refine MeasureTheory.integrableOn_Ioi_deriv_of_nonneg' (l := 0)
    (fun t ht => ?_) (fun t ht => ?_) kW_antideriv_tendsto
  · rw [Set.mem_Ici] at ht
    exact kW_hasDerivAt_antideriv (by linarith)
  · rw [Set.mem_Ioi] at ht
    have ht1 : (1:ℝ) < t := by linarith
    have hl : 0 < Real.log t := Real.log_pos ht1
    rw [Work.RHContract.kW]
    positivity

end Work.RHContract.A
