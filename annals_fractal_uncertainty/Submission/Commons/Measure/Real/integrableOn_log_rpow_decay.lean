import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

namespace Commons.Measure.Real

open MeasureTheory Set Filter
open scoped ENNReal Topology

/-- Auxiliary: derivative facts for the antiderivative `t ↦ (log t)^(1-β)/(1-β)` of
`t ↦ t⁻¹ (log t)^{-β}`, valid for `t > 1`. -/
private lemma log_rpow_antideriv (β : ℝ) (hβ : 1 < β) {c : ℝ} (hc : 1 < c) :
    (∀ x ∈ Set.Ici c, HasDerivAt (fun t : ℝ => (Real.log t) ^ (1 - β) / (1 - β))
        (x⁻¹ / (Real.log x) ^ β) x) ∧
    (∀ x ∈ Set.Ioi c, 0 ≤ x⁻¹ / (Real.log x) ^ β) ∧
    Tendsto (fun t : ℝ => (Real.log t) ^ (1 - β) / (1 - β)) atTop (𝓝 0) := by
  refine ⟨?_, ?_, ?_⟩
  · intro x hx
    have hx1 : 1 < x := lt_of_lt_of_le hc hx
    have hx0 : x ≠ 0 := by linarith
    have hlog : 0 < Real.log x := Real.log_pos hx1
    have h1 : HasDerivAt (fun t : ℝ => Real.log t) x⁻¹ x := Real.hasDerivAt_log hx0
    have h2 : HasDerivAt (fun t : ℝ => (Real.log t) ^ (1 - β))
        (x⁻¹ * (1 - β) * (Real.log x) ^ ((1 - β) - 1)) x :=
      h1.rpow_const (Or.inl (ne_of_gt hlog))
    have h3 : HasDerivAt (fun t : ℝ => (Real.log t) ^ (1 - β) / (1 - β))
        ((x⁻¹ * (1 - β) * (Real.log x) ^ ((1 - β) - 1)) / (1 - β)) x :=
      h2.div_const (1 - β)
    convert h3 using 1
    rw [show (1 : ℝ) - β - 1 = -β by ring, Real.rpow_neg (le_of_lt hlog)]
    have hne : (1 - β) ≠ 0 := by linarith
    have hne2 : (Real.log x) ^ β ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos hlog β)
    field_simp
  · intro x hx
    have hx1 : 1 < x := lt_trans hc hx
    have hlog : 0 < Real.log x := Real.log_pos hx1
    have hx0 : 0 < x := by linarith
    exact div_nonneg (inv_pos.mpr hx0).le (Real.rpow_pos_of_pos hlog β).le
  · have h1 : Tendsto (fun t : ℝ => (Real.log t) ^ (1 - β)) atTop (𝓝 0) := by
      convert (tendsto_rpow_neg_atTop (show (0 : ℝ) < β - 1 by linarith)).comp
        Real.tendsto_log_atTop using 1
      ext t
      simp [Function.comp_apply, neg_sub]
    simpa using h1.div_const (1 - β)

/-- Auxiliary integrability: `t ↦ t⁻¹ (log t)^{-β}` is integrable on `(c, ∞)` for
`β > 1`, `c > 1`. -/
private lemma integrableOn_inv_div_log_rpow_Ioi (β : ℝ) (hβ : 1 < β) {c : ℝ} (hc : 1 < c) :
    IntegrableOn (fun t : ℝ => t⁻¹ / (Real.log t) ^ β) (Set.Ioi c) := by
  obtain ⟨hd, hpos, hlim⟩ := log_rpow_antideriv β hβ hc
  exact integrableOn_Ioi_deriv_of_nonneg' hd hpos hlim

/-- On `(0, 2]` the comparison function is bounded by the constant `2 / (log 2)^β`. -/
private lemma psi_le_const (β : ℝ) (hβ : 1 < β) {r : ℝ} (hr : r ∈ Set.Ioc 0 2) :
    r / (Real.log (2 + r)) ^ β / (1 + r ^ 2) ≤ 2 / (Real.log 2) ^ β := by
  have hβ0 : 0 < β := by linarith
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hr0 : 0 ≤ r := hr.1.le
  have hr2 : r ≤ 2 := hr.2
  have hlog_pos : 0 < Real.log (2 + r) := Real.log_pos (by linarith)
  have hlog_mono : Real.log 2 ≤ Real.log (2 + r) := Real.log_le_log (by norm_num) (by linarith)
  have hpow : (Real.log 2) ^ β ≤ (Real.log (2 + r)) ^ β :=
    Real.rpow_le_rpow hlog2.le hlog_mono hβ0.le
  have hnum : 0 ≤ r / (Real.log (2 + r)) ^ β :=
    div_nonneg hr0 (Real.rpow_pos_of_pos hlog_pos β).le
  have step1 : r / (Real.log (2 + r)) ^ β / (1 + r ^ 2) ≤ r / (Real.log (2 + r)) ^ β := by
    have := div_le_div_of_nonneg_left hnum (show (0 : ℝ) < 1 by norm_num)
      (show (1 : ℝ) ≤ 1 + r ^ 2 by nlinarith [sq_nonneg r])
    simpa using this
  have step2 : r / (Real.log (2 + r)) ^ β ≤ 2 / (Real.log (2 + r)) ^ β :=
    div_le_div_of_nonneg_right hr2 (Real.rpow_pos_of_pos hlog_pos β).le
  have step3 : 2 / (Real.log (2 + r)) ^ β ≤ 2 / (Real.log 2) ^ β :=
    div_le_div_of_nonneg_left (by norm_num) (Real.rpow_pos_of_pos hlog2 β) hpow
  exact step1.trans (step2.trans step3)

/-- On `(2, ∞)` the comparison function is dominated by `t ↦ t⁻¹ (log t)^{-β}`. -/
private lemma psi_le_inv_div_log (β : ℝ) (hβ : 1 < β) {r : ℝ} (hr : 2 < r) :
    r / (Real.log (2 + r)) ^ β / (1 + r ^ 2) ≤ r⁻¹ / (Real.log r) ^ β := by
  have hβ0 : 0 < β := by linarith
  have hr0 : 0 < r := by linarith
  have hr1 : 1 < r := by linarith
  have hlogr : 0 < Real.log r := Real.log_pos hr1
  have hlog_mono : Real.log r ≤ Real.log (2 + r) := Real.log_le_log hr0 (by linarith)
  have hpow : (Real.log r) ^ β ≤ (Real.log (2 + r)) ^ β :=
    Real.rpow_le_rpow hlogr.le hlog_mono hβ0.le
  have step1 : r / (Real.log (2 + r)) ^ β ≤ r / (Real.log r) ^ β :=
    div_le_div_of_nonneg_left hr0.le (Real.rpow_pos_of_pos hlogr β) hpow
  have step12 : r / (Real.log (2 + r)) ^ β / (1 + r ^ 2) ≤ r / (Real.log r) ^ β / (1 + r ^ 2) :=
    div_le_div_of_nonneg_right step1 (by positivity : (0 : ℝ) ≤ 1 + r ^ 2)
  have hden : r ^ 2 ≤ 1 + r ^ 2 := by nlinarith [sq_nonneg r]
  have hnum : 0 ≤ r / (Real.log r) ^ β :=
    div_nonneg hr0.le (Real.rpow_pos_of_pos hlogr β).le
  have step2 : r / (Real.log r) ^ β / (1 + r ^ 2) ≤ r / (Real.log r) ^ β / r ^ 2 :=
    div_le_div_of_nonneg_left hnum (by positivity : (0 : ℝ) < r ^ 2) hden
  have step3 : r / (Real.log r) ^ β / r ^ 2 = r⁻¹ / (Real.log r) ^ β := by
    field_simp
  exact step12.trans (step2.trans (le_of_eq step3))

/-- **The comparison function of the Beurling–Malliavin growth condition is integrable.**
For `β > 1`, `r ↦ r / (log (2 + r)) ^ β / (1 + r ^ 2)` is integrable on `(0, ∞)`.
(The same file `Submission/Commons/Measure/Real/integral_log_rpow_decay.lean` proves the
`∫⁻` bound for this function with private lemmas; this exposes the integrability.) -/
theorem integrableOn_log_rpow_decay (β : ℝ) (hβ : 1 < β) :
    IntegrableOn (fun r : ℝ => r / (Real.log (2 + r)) ^ β / (1 + r ^ 2)) (Set.Ioi 0) := by
  have hmeas : Measurable (fun r : ℝ => r / (Real.log (2 + r)) ^ β / (1 + r ^ 2)) := by
    measurability
  -- Left part `(0, 2]`: dominated by a constant on a finite measure set.
  have hleft : IntegrableOn (fun r : ℝ => r / (Real.log (2 + r)) ^ β / (1 + r ^ 2))
      (Set.Ioc 0 2) := by
    refine Integrable.mono' (g := fun _ : ℝ => 2 / (Real.log 2) ^ β)
      (integrableOn_const (μ := volume) (s := Set.Ioc (0 : ℝ) 2)
        (C := 2 / (Real.log 2) ^ β) (by rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top))
      hmeas.aestronglyMeasurable ?_
    rw [ae_restrict_iff' measurableSet_Ioc]
    filter_upwards with r hr
    rw [Real.norm_of_nonneg]
    · exact psi_le_const β hβ hr
    · exact div_nonneg (div_nonneg hr.1.le
        (Real.rpow_pos_of_pos (Real.log_pos (by have := hr.1; linarith)) β).le) (by positivity)
  -- Right part `(2, ∞)`: dominated by the integrable `t ↦ t⁻¹ (log t)^{-β}`.
  have hright : IntegrableOn (fun r : ℝ => r / (Real.log (2 + r)) ^ β / (1 + r ^ 2))
      (Set.Ioi 2) := by
    have hbase : IntegrableOn (fun t : ℝ => t⁻¹ / (Real.log t) ^ β) (Set.Ioi 2) :=
      integrableOn_inv_div_log_rpow_Ioi β hβ (by norm_num)
    refine hbase.mono' hmeas.aestronglyMeasurable ?_
    rw [ae_restrict_iff' measurableSet_Ioi]
    filter_upwards with r hr
    have hr2 : (2 : ℝ) < r := hr
    rw [Real.norm_of_nonneg]
    · exact psi_le_inv_div_log β hβ hr2
    · exact div_nonneg (div_nonneg (by linarith)
        (Real.rpow_pos_of_pos (Real.log_pos (by linarith)) β).le) (by positivity)
  have hunion := hleft.union hright
  rwa [Set.Ioc_union_Ioi_eq_Ioi (by norm_num : (0 : ℝ) ≤ 2)] at hunion

end Commons.Measure.Real