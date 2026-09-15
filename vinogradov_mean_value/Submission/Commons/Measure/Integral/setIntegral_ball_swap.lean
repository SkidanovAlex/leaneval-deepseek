import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Prod

namespace Commons.Measure.Integral

open MeasureTheory
open scoped ENNReal

section Aux

variable {E : Type*} [PseudoMetricSpace E] [MeasurableSpace E] [BorelSpace E]
  [SecondCountableTopology E]

/-- General form of the ball-average Fubini symmetry. -/
lemma setIntegral_ball_swap_aux (μ : Measure E) [SFinite μ] (F W : E → ℝ)
    (hFm : Measurable F) (hWm : Measurable W) (hF0 : 0 ≤ F) (hW0 : 0 ≤ W)
    {M : ℝ} (hM : ∀ x, F x ≤ M) (hWint : Integrable W μ) {R : ℝ} {KW : ℝ}
    (hKW0 : 0 ≤ KW)
    (hKW : ∀ x : E, (∫ c' in Metric.ball x R, W c' ∂μ) ≤ KW * W x) :
    (∫ x, F x * (∫ c' in Metric.ball x R, W c' ∂μ) ∂μ)
      = ∫ c', W c' * (∫ x in Metric.ball c' R, F x ∂μ) ∂μ := by
  classical
  set f : E → E → ℝ := fun x c' => if dist x c' < R then F x * W c' else 0 with hfdef
  have hf_apply : ∀ x c', f x c' = if dist x c' < R then F x * W c' else 0 :=
    fun x c' => by rw [hfdef]
  -- pointwise nonnegativity
  have hfnn_pt : ∀ p : E × E, 0 ≤ Function.uncurry f p := by
    intro p
    change 0 ≤ f p.1 p.2
    rw [hf_apply]
    split_ifs with h
    · exact mul_nonneg (hF0 p.1) (hW0 p.2)
    · exact le_refl 0
  have hfnn : 0 ≤ᵐ[μ.prod μ] Function.uncurry f := Filter.Eventually.of_forall hfnn_pt
  -- measurability of uncurry f
  have hfmeas : Measurable (Function.uncurry f) := by
    have h_eq : Function.uncurry f =
        ({p : E × E | dist p.1 p.2 < R}).indicator (fun p => F p.1 * W p.2) := by
      funext p
      change (if dist p.1 p.2 < R then F p.1 * W p.2 else 0) = _
      rw [Set.indicator_apply]
      by_cases h : dist p.1 p.2 < R <;> simp [h]
    rw [h_eq]
    exact Measurable.indicator ((hFm.comp measurable_fst).mul (hWm.comp measurable_snd))
      (measurableSet_lt measurable_dist measurable_const)
  -- ball-average of W, in ENNReal form, bounded by KW * W x
  have hWlin : ∫⁻ x, ENNReal.ofReal (W x) ∂μ = ENNReal.ofReal (∫ x, W x ∂μ) :=
    (ofReal_integral_eq_lintegral_ofReal hWint (Filter.Eventually.of_forall hW0)).symm
  have hWlin_lt : ∫⁻ x, ENNReal.ofReal (W x) ∂μ < ∞ := by
    rw [hWlin]; exact ENNReal.ofReal_lt_top
  have hinner_le : ∀ x, (∫⁻ c' in Metric.ball x R, ENNReal.ofReal (W c') ∂μ)
      ≤ ENNReal.ofReal KW * ENNReal.ofReal (W x) := by
    intro x
    have hball_int : Integrable ((Metric.ball x R).indicator W) μ :=
      hWint.indicator measurableSet_ball
    have hball_nn : 0 ≤ᵐ[μ] ((Metric.ball x R).indicator W) := by
      filter_upwards with y
      simp only [Set.indicator_apply]
      split_ifs with h
      · exact hW0 y
      · exact le_refl 0
    calc ∫⁻ c' in Metric.ball x R, ENNReal.ofReal (W c') ∂μ
        = ∫⁻ c', ENNReal.ofReal ((Metric.ball x R).indicator W c') ∂μ := by
          rw [← lintegral_indicator measurableSet_ball]
          apply lintegral_congr; intro c'
          by_cases h : c' ∈ Metric.ball x R
          · simp only [Set.indicator_of_mem h]
          · simp only [Set.indicator_of_notMem h, ENNReal.ofReal_zero]
      _ = ENNReal.ofReal (∫ c', (Metric.ball x R).indicator W c' ∂μ) :=
          (ofReal_integral_eq_lintegral_ofReal hball_int hball_nn).symm
      _ = ENNReal.ofReal (∫ c' in Metric.ball x R, W c' ∂μ) := by
          rw [integral_indicator measurableSet_ball]
      _ ≤ ENNReal.ofReal (KW * W x) := ENNReal.ofReal_le_ofReal (hKW x)
      _ = ENNReal.ofReal KW * ENNReal.ofReal (W x) := ENNReal.ofReal_mul hKW0
  -- inner = ofReal (F x) * ball-average
  have hinner : ∀ x, (∫⁻ c', ENNReal.ofReal (f x c') ∂μ)
      = ENNReal.ofReal (F x) * (∫⁻ c' in Metric.ball x R, ENNReal.ofReal (W c') ∂μ) := by
    intro x
    have hpt : ∀ c', ENNReal.ofReal (f x c') = ENNReal.ofReal (F x) *
        (Metric.ball x R).indicator (fun c' => ENNReal.ofReal (W c')) c' := by
      intro c'
      rw [hf_apply]
      by_cases h : dist x c' < R
      · have hc : c' ∈ Metric.ball x R := by rw [Metric.mem_ball]; rwa [dist_comm]
        rw [if_pos h, Set.indicator_of_mem hc, ENNReal.ofReal_mul (hF0 x)]
      · have hc : c' ∉ Metric.ball x R := by
          rw [Metric.mem_ball]; exact fun h' => h (by rwa [dist_comm] at h')
        rw [if_neg h, Set.indicator_of_notMem hc, ENNReal.ofReal_zero, mul_zero]
    calc ∫⁻ c', ENNReal.ofReal (f x c') ∂μ
        = ∫⁻ c', ENNReal.ofReal (F x) *
            (Metric.ball x R).indicator (fun c' => ENNReal.ofReal (W c')) c' ∂μ :=
          lintegral_congr hpt
      _ = ENNReal.ofReal (F x) *
            ∫⁻ c', (Metric.ball x R).indicator (fun c' => ENNReal.ofReal (W c')) c' ∂μ :=
          lintegral_const_mul _ (Measurable.indicator hWm.ennreal_ofReal measurableSet_ball)
      _ = ENNReal.ofReal (F x) *
            (∫⁻ c' in Metric.ball x R, ENNReal.ofReal (W c') ∂μ) := by
          rw [lintegral_indicator measurableSet_ball]
  -- integrability of uncurry f
  have hfint : Integrable (Function.uncurry f) (μ.prod μ) := by
    refine ⟨hfmeas.aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal hfnn]
    have hprod : ∫⁻ p : E × E, ENNReal.ofReal (Function.uncurry f p) ∂(μ.prod μ)
        = ∫⁻ x, ∫⁻ c', ENNReal.ofReal (f x c') ∂μ ∂μ := by
      have hm : AEMeasurable (Function.uncurry fun x c' => ENNReal.ofReal (f x c')) (μ.prod μ) :=
        hfmeas.ennreal_ofReal.aemeasurable
      exact (lintegral_lintegral hm).symm
    rw [hprod]
    calc ∫⁻ x, ∫⁻ c', ENNReal.ofReal (f x c') ∂μ ∂μ
        = ∫⁻ x, ENNReal.ofReal (F x) *
            (∫⁻ c' in Metric.ball x R, ENNReal.ofReal (W c') ∂μ) ∂μ := by
          apply lintegral_congr; intro x; rw [hinner x]
      _ ≤ ∫⁻ x, ENNReal.ofReal (F x) *
            (ENNReal.ofReal KW * ENNReal.ofReal (W x)) ∂μ := by
          apply lintegral_mono; intro x
          exact mul_le_mul_right (hinner_le x) _
      _ ≤ ∫⁻ x, ENNReal.ofReal M *
            (ENNReal.ofReal KW * ENNReal.ofReal (W x)) ∂μ := by
          apply lintegral_mono; intro x
          exact mul_le_mul_left (ENNReal.ofReal_le_ofReal (hM x)) _
      _ = ENNReal.ofReal M * ∫⁻ x, ENNReal.ofReal KW * ENNReal.ofReal (W x) ∂μ := by
          rw [lintegral_const_mul (ENNReal.ofReal M)
            (f := fun x => ENNReal.ofReal KW * ENNReal.ofReal (W x)) (by fun_prop)]
      _ = ENNReal.ofReal M * (ENNReal.ofReal KW * ∫⁻ x, ENNReal.ofReal (W x) ∂μ) := by
          rw [lintegral_const_mul (ENNReal.ofReal KW)
            (f := fun x => ENNReal.ofReal (W x)) (by fun_prop)]
      _ < ∞ := by
          rw [← mul_assoc]
          exact ENNReal.mul_lt_top
            (ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top) hWlin_lt
  have hswap := integral_integral_swap (ν := μ) hfint
  have hL : (∫ x, F x * (∫ c' in Metric.ball x R, W c' ∂μ) ∂μ)
      = ∫ x, ∫ c', f x c' ∂μ ∂μ := by
    apply integral_congr_ae
    filter_upwards with x
    have h1 : F x * (∫ c' in Metric.ball x R, W c' ∂μ) = ∫ c', f x c' ∂μ := by
      rw [← integral_indicator measurableSet_ball,
        ← integral_const_mul (F x) (fun c' => (Metric.ball x R).indicator W c')]
      apply integral_congr_ae
      filter_upwards with c'
      rw [hf_apply]
      by_cases h : dist x c' < R
      · have hc : c' ∈ Metric.ball x R := by rw [Metric.mem_ball]; rwa [dist_comm]
        rw [if_pos h, Set.indicator_of_mem hc]
      · have hc : c' ∉ Metric.ball x R := by
          rw [Metric.mem_ball]; exact fun h' => h (by rwa [dist_comm] at h')
        rw [if_neg h, Set.indicator_of_notMem hc, mul_zero]
    exact h1
  have hR : (∫ c', W c' * (∫ x in Metric.ball c' R, F x ∂μ) ∂μ)
      = ∫ c', ∫ x, f x c' ∂μ ∂μ := by
    apply integral_congr_ae
    filter_upwards with c'
    have h1 : W c' * (∫ x in Metric.ball c' R, F x ∂μ) = ∫ x, f x c' ∂μ := by
      rw [← integral_indicator measurableSet_ball,
        ← integral_const_mul (W c') (fun x => (Metric.ball c' R).indicator F x)]
      apply integral_congr_ae
      filter_upwards with x
      rw [hf_apply]
      by_cases h : dist x c' < R
      · have hc : x ∈ Metric.ball c' R := by rwa [Metric.mem_ball]
        rw [if_pos h, Set.indicator_of_mem hc]; ring
      · have hc : x ∉ Metric.ball c' R := by
          rw [Metric.mem_ball]; exact fun h' => h h'
        rw [if_neg h, Set.indicator_of_notMem hc, mul_zero]
    exact h1
  calc (∫ x, F x * (∫ c' in Metric.ball x R, W c' ∂μ) ∂μ)
      = ∫ x, ∫ c', f x c' ∂μ ∂μ := hL
    _ = ∫ c', ∫ x, f x c' ∂μ ∂μ := hswap
    _ = ∫ c', W c' * (∫ x in Metric.ball c' R, F x ∂μ) ∂μ := hR.symm

end Aux

/-- **Symmetry of the ball average** (Fubini for the symmetric ball relation on `ℝᵏ`).
For measurable `F ≥ 0` bounded above by `M` and `W ≥ 0` integrable satisfying the
ball-average bound `∫_{B(x,R)} W ≤ KW · W(x)`,
`∫_x F(x) · ∫_{B(x,R)} W = ∫_{c'} W(c') · ∫_{B(c',R)} F`. -/
theorem setIntegral_ball_swap (k : ℕ) (F W : EuclideanSpace ℝ (Fin k) → ℝ)
    (hFm : Measurable F) (hWm : Measurable W) (hF0 : 0 ≤ F) (hW0 : 0 ≤ W)
    {M : ℝ} (hM : ∀ x, F x ≤ M) (hWint : Integrable W volume) {R : ℝ} {KW : ℝ}
    (hKW0 : 0 ≤ KW)
    (hKW : ∀ x : EuclideanSpace ℝ (Fin k),
      (∫ c' in Metric.ball x R, W c') ≤ KW * W x) :
    (∫ x : EuclideanSpace ℝ (Fin k), F x * (∫ c' in Metric.ball x R, W c'))
      = ∫ c' : EuclideanSpace ℝ (Fin k), W c' * (∫ x in Metric.ball c' R, F x) := by
  exact setIntegral_ball_swap_aux volume F W hFm hWm hF0 hW0 hM hWint hKW0 hKW

end Commons.Measure.Integral