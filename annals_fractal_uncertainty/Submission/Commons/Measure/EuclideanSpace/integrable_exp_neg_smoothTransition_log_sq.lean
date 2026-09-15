import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
import Mathlib.Analysis.SpecialFunctions.SmoothTransition

namespace Commons.Measure.EuclideanSpace

open MeasureTheory Real Filter Asymptotics
open scoped Topology ENNReal

/-- For `0 < c` and `0 < m`, the function `t ↦ exp(-(c * t / (log (2+t))^2))` is bounded
above by `(1+t)^{-m}` for all sufficiently large `t`. -/
theorem exists_forall_ge_exp_neg_div_log_sq_le_rpow (c : ℝ) (hc : 0 < c) (m : ℝ)
    (hm : 0 < m) :
    ∃ R : ℝ, ∀ t : ℝ, R ≤ t →
      Real.exp (-(c * (t / (Real.log (2 + t)) ^ 2))) ≤ (1 + t) ^ (-m) := by
  have hlittle : (fun t : ℝ => Real.log (2 + t) ^ 3) =o[atTop] (fun t : ℝ => t) := by
    have h1 : (fun t : ℝ => Real.log (2 + t) ^ 3) =o[atTop] (fun t : ℝ => 2 + t) :=
      (Real.isLittleO_pow_log_id_atTop (n := 3)).comp_tendsto
        (tendsto_atTop_add_const_left _ _ tendsto_id)
    have h2 : (fun t : ℝ => 2 + t) =O[atTop] (fun t : ℝ => t) := by
      rw [isBigO_iff]
      refine ⟨2, ?_⟩
      filter_upwards [eventually_ge_atTop (2:ℝ)] with t ht
      rw [Real.norm_of_nonneg (by linarith), Real.norm_of_nonneg (by linarith)]
      linarith
    exact h1.trans_isBigO h2
  have hb : ∀ᶠ t in atTop, Real.log (2 + t) ^ 3 ≤ (c / m) * t := by
    have hb0 := hlittle.bound (show 0 < c / m by positivity)
    filter_upwards [hb0, eventually_ge_atTop (0:ℝ)] with t ht ht0
    rwa [Real.norm_of_nonneg (pow_nonneg (Real.log_nonneg (by linarith)) 3),
        Real.norm_of_nonneg ht0] at ht
  obtain ⟨R₀, hR₀⟩ := eventually_atTop.mp hb
  refine ⟨max R₀ 0, ?_⟩
  intro t ht
  have ht0 : 0 ≤ t := le_trans (le_max_right _ _) ht
  have htR₀ : R₀ ≤ t := le_trans (le_max_left _ _) ht
  have hlog2pos : 0 < Real.log (2 + t) := Real.log_pos (by linarith)
  have hmain : m * Real.log (1 + t) * (Real.log (2 + t)) ^ 2 ≤ c * t := by
    have hb' := hR₀ t htR₀
    have hstep1 : m * Real.log (1 + t) * (Real.log (2 + t))^2 ≤ m * (Real.log (2 + t))^3 := by
      have hlog1le : Real.log (1 + t) ≤ Real.log (2 + t) :=
        Real.log_le_log (by linarith) (by linarith)
      have hle : Real.log (1 + t) * (Real.log (2 + t))^2 ≤ (Real.log (2 + t))^3 := by
        calc Real.log (1 + t) * (Real.log (2 + t))^2
            ≤ Real.log (2 + t) * (Real.log (2 + t))^2 :=
              mul_le_mul_of_nonneg_right hlog1le (sq_nonneg _)
          _ = (Real.log (2 + t))^3 := by ring
      calc m * Real.log (1 + t) * (Real.log (2 + t))^2
          = m * (Real.log (1 + t) * (Real.log (2 + t))^2) := by ring
        _ ≤ m * (Real.log (2 + t))^3 := mul_le_mul_of_nonneg_left hle hm.le
    have hstep2 : m * (Real.log (2 + t))^3 ≤ c * t := by
      have h := mul_le_mul_of_nonneg_left hb' hm.le
      calc m * (Real.log (2 + t))^3 ≤ m * ((c/m) * t) := h
        _ = c * t := by field_simp
    linarith
  rw [Real.rpow_def_of_pos (by linarith : (0:ℝ) < 1 + t),
      show Real.log (1 + t) * (-m) = -(m * Real.log (1 + t)) by ring,
      Real.exp_le_exp, neg_le_neg_iff, ← mul_div_assoc,
      le_div_iff₀ (by positivity : 0 < (Real.log (2 + t))^2)]
  exact hmain

/-- Measurability of the integrand of `integrable_exp_neg_smoothTransition_log_sq`. -/
theorem measurable_exp_neg_smoothTransition_log_sq (d : ℕ) (c : ℝ) :
    Measurable (fun x : EuclideanSpace ℝ (Fin d) =>
      Real.exp (-(c * (Real.smoothTransition (‖x‖ / 5 - 1) *
        (‖x‖ / (Real.log (2 + ‖x‖)) ^ 2))))) := by
  measurability

open MeasureTheory Real in
/-- The function `x ↦ exp(-(c * χ(|x|) * |x| / (log (2+|x|))^2))`, where `χ` is the smooth
transition function composed with `t ↦ t/5 - 1`, is integrable on `EuclideanSpace ℝ (Fin d)`. -/
theorem integrable_exp_neg_smoothTransition_log_sq (d : ℕ) {c : ℝ} (hc : 0 < c) :
    Integrable (fun x : EuclideanSpace ℝ (Fin d) =>
      Real.exp (-(c * (Real.smoothTransition (‖x‖ / 5 - 1)
        * (‖x‖ / (Real.log (2 + ‖x‖)) ^ 2)))))
      (MeasureTheory.volume : Measure (EuclideanSpace ℝ (Fin d))) := by
  obtain ⟨R₁, hR₁⟩ :=
    exists_forall_ge_exp_neg_div_log_sq_le_rpow c hc ((d:ℝ) + 1) (by positivity)
  have hmeas : AEStronglyMeasurable (fun x : EuclideanSpace ℝ (Fin d) =>
      Real.exp (-(c * (Real.smoothTransition (‖x‖ / 5 - 1)
        * (‖x‖ / (Real.log (2 + ‖x‖)) ^ 2))))) volume :=
    (measurable_exp_neg_smoothTransition_log_sq d c).aestronglyMeasurable
  have hvol : (volume : Measure (EuclideanSpace ℝ (Fin d)))
      (Metric.closedBall 0 (max R₁ 10)) ≠ ∞ := by
    rw [← lt_top_iff_ne_top]
    exact (isCompact_closedBall 0 (max R₁ 10)).measure_lt_top
  have h1 : Integrable ((Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) (max R₁ 10)).indicator
      (fun _ => (1:ℝ))) volume := by
    rw [integrable_indicator_iff measurableSet_closedBall]
    exact integrableOn_const hvol (by simp)
  have h2 : Integrable (fun x : EuclideanSpace ℝ (Fin d) =>
      (1 + ‖x‖) ^ (-((d:ℝ) + 1))) volume := by
    apply integrable_one_add_norm
    rw [finrank_euclideanSpace, Fintype.card_fin]
    linarith
  refine (h1.add h2).mono' hmeas ?_
  filter_upwards with x
  rw [Real.norm_of_nonneg (Real.exp_nonneg _), Pi.add_apply]
  by_cases hx : ‖x‖ ≤ max R₁ 10
  · have hmem : x ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) (max R₁ 10) := by
      simpa [Metric.mem_closedBall] using hx
    rw [Set.indicator_of_mem hmem (fun _ => (1:ℝ))]
    have hexp_le_one : Real.exp (-(c * (Real.smoothTransition (‖x‖/5 - 1) *
        (‖x‖ / (Real.log (2 + ‖x‖))^2)))) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      have hnn : 0 ≤ Real.smoothTransition (‖x‖/5 - 1) * (‖x‖ / (Real.log (2 + ‖x‖))^2) :=
        mul_nonneg (Real.smoothTransition.nonneg _)
          (div_nonneg (norm_nonneg _) (sq_nonneg _))
      exact neg_nonpos.mpr (mul_nonneg hc.le hnn)
    have hpow_nonneg : 0 ≤ (1 + ‖x‖) ^ (-((d:ℝ)+1)) := by positivity
    linarith
  · have hmem : x ∉ Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) (max R₁ 10) := by
      simpa [Metric.mem_closedBall] using hx
    rw [Set.indicator_of_notMem hmem (fun _ => (1:ℝ)), zero_add]
    have hle : max R₁ 10 ≤ ‖x‖ := le_of_lt (lt_of_not_ge hx)
    have hR₁le : R₁ ≤ ‖x‖ := le_trans (le_max_left _ _) hle
    have h10le : (10:ℝ) ≤ ‖x‖ := le_trans (le_max_right _ _) hle
    have hchi : Real.smoothTransition (‖x‖/5 - 1) = 1 :=
      Real.smoothTransition.one_of_one_le (by linarith)
    rw [hchi, one_mul]
    exact hR₁ ‖x‖ hR₁le

end Commons.Measure.EuclideanSpace