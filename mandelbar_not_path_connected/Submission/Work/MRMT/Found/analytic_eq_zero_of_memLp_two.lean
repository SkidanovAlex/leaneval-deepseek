import Mathlib
import Submission.Work.MRMT.Weyl.integral_ball_eq_mul_of_differentiable

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.MRMT.Found

open MeasureTheory Metric

noncomputable section

/-- Lebesgue measure of a ball in `ℂ`, expressed as a real number. -/
lemma real_volume_ball (c : ℂ) {R : ℝ} (hR : 0 ≤ R) :
    (volume (Metric.ball c R)).toReal = R ^ 2 * Real.pi := by
  rw [Complex.volume_ball, ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_ofReal hR]
  simp [NNReal.coe_real_pi]

/-- The integral of the constant function `1` over a ball in `ℂ`. -/
lemma integral_indicator_one_ball (c : ℂ) {R : ℝ} (hR : 0 ≤ R) :
    ∫ z : ℂ, (Metric.ball c R).indicator (fun _ => (1 : ℝ)) z = R ^ 2 * Real.pi := by
  rw [MeasureTheory.integral_indicator measurableSet_ball, MeasureTheory.setIntegral_const]
  rw [smul_eq_mul, mul_one, MeasureTheory.Measure.real_def, real_volume_ball c hR]

/-- Cauchy–Schwarz (Hölder's inequality with `p = q = 2`) on a ball for an `L²` function. -/
lemma setIntegral_norm_le_of_memLp_two {F : ℂ → ℂ}
    (h2 : MeasureTheory.MemLp F 2 (volume : Measure ℂ)) (c : ℂ) {R : ℝ} (hR : 0 < R) :
    ∫ z in Metric.ball c R, ‖F z‖
      ≤ Real.sqrt (∫ z, ‖F z‖ ^ 2) * Real.sqrt (Real.pi * R ^ 2) := by
  have hpq : (2 : ℝ).HolderConjugate 2 := by
    rw [Real.holderConjugate_iff]; constructor <;> norm_num
  set g : ℂ → ℝ := (Metric.ball c R).indicator (fun _ => (1 : ℝ)) with hgdef
  have hvolne : volume (Metric.ball c R) ≠ ⊤ := by
    rw [Complex.volume_ball]
    exact ENNReal.mul_ne_top (ENNReal.pow_ne_top ENNReal.ofReal_ne_top) ENNReal.coe_ne_top
  have hg_mem : MeasureTheory.MemLp g (ENNReal.ofReal (2 : ℝ)) volume := by
    rw [hgdef]
    exact MeasureTheory.memLp_indicator_const _ measurableSet_ball _ (Or.inr hvolne)
  have hf_mem : MeasureTheory.MemLp (fun z : ℂ => ‖F z‖) (ENNReal.ofReal (2 : ℝ)) volume := by
    simpa using h2.norm
  have hholder := MeasureTheory.integral_mul_le_Lp_mul_Lq_of_nonneg (μ := volume)
      (p := 2) (q := 2) hpq
      (Filter.Eventually.of_forall (fun z => norm_nonneg _))
      (Filter.Eventually.of_forall (fun z => by
        rw [hgdef]; exact Set.indicator_nonneg (fun _ _ => by norm_num) z))
      hf_mem hg_mem
  have hL : ∫ z, ‖F z‖ * g z = ∫ z in Metric.ball c R, ‖F z‖ := by
    rw [hgdef]
    rw [← MeasureTheory.integral_indicator (μ := volume) (f := fun z => ‖F z‖) measurableSet_ball]
    apply MeasureTheory.integral_congr_ae
    filter_upwards with z
    by_cases hz : z ∈ Metric.ball c R
    · rw [Set.indicator_of_mem hz, Set.indicator_of_mem hz, mul_one]
    · rw [Set.indicator_of_notMem hz, Set.indicator_of_notMem hz, mul_zero]
  have hR1 : (∫ z, ‖F z‖ ^ (2 : ℝ)) = ∫ z, ‖F z‖ ^ 2 := by
    apply MeasureTheory.integral_congr_ae
    exact Filter.Eventually.of_forall (fun z => Real.rpow_two _)
  have hR2 : (∫ z, g z ^ (2 : ℝ)) = Real.pi * R ^ 2 := by
    have hfun : (fun z => g z ^ (2 : ℝ))
        = (fun z => (Metric.ball c R).indicator (fun _ => (1 : ℝ)) z) := by
      funext z
      rw [Real.rpow_two, hgdef]
      by_cases hz : z ∈ Metric.ball c R
      · rw [Set.indicator_of_mem hz]; norm_num
      · rw [Set.indicator_of_notMem hz]; norm_num
    rw [hfun, integral_indicator_one_ball c (le_of_lt hR)]
    ring
  have he1 : Real.sqrt (∫ z, ‖F z‖ ^ 2) = (∫ z, ‖F z‖ ^ (2 : ℝ)) ^ (1 / 2 : ℝ) := by
    rw [← hR1, Real.sqrt_eq_rpow]
  have he2 : Real.sqrt (Real.pi * R ^ 2) = (∫ z, g z ^ (2 : ℝ)) ^ (1 / 2 : ℝ) := by
    rw [← hR2, Real.sqrt_eq_rpow]
  rw [he1, he2, ← hL]
  exact hholder

theorem analytic_eq_zero_of_memLp_two {F : ℂ → ℂ} (hF : AnalyticOn ℂ F Set.univ)
    (h2 : MeasureTheory.MemLp F 2 (MeasureTheory.volume : MeasureTheory.Measure ℂ)) : F = 0 := by
  have hdiff : Differentiable ℂ F := by
    rw [← differentiableOn_univ]
    exact hF.differentiableOn
  set C : ℝ := ∫ z, ‖F z‖ ^ 2 with hCdef
  have hCnn : 0 ≤ C := by
    rw [hCdef]; exact MeasureTheory.integral_nonneg (fun z => by positivity)
  funext c
  have ht : ‖F c‖ ^ 2 = 0 := by
    by_contra hne
    have htpos : 0 < ‖F c‖ ^ 2 := lt_of_le_of_ne (by positivity) (Ne.symm hne)
    have hineq : ∀ R : ℝ, 0 < R → ‖F c‖ ^ 2 * R ^ 2 ≤ C / Real.pi := by
      intro R hR
      have hcs := setIntegral_norm_le_of_memLp_two h2 c hR
      rw [← hCdef] at hcs
      have hMV := Work.MRMT.Weyl.integral_ball_eq_mul_of_differentiable hdiff (c := c) hR
      have h1 : ‖∫ z in Metric.ball c R, F z‖ ≤ ∫ z in Metric.ball c R, ‖F z‖ := by
        rw [← MeasureTheory.integral_indicator (μ := volume) (f := F) measurableSet_ball,
            ← MeasureTheory.integral_indicator (μ := volume) (f := fun z => ‖F z‖)
              measurableSet_ball]
        refine (MeasureTheory.norm_integral_le_integral_norm
          (fun z => (Metric.ball c R).indicator F z)).trans ?_
        apply le_of_eq
        apply MeasureTheory.integral_congr_ae
        filter_upwards with z
        by_cases hz : z ∈ Metric.ball c R
        · rw [Set.indicator_of_mem hz, Set.indicator_of_mem hz]
        · rw [Set.indicator_of_notMem hz, Set.indicator_of_notMem hz, norm_zero]
      have hle : (Real.pi * R ^ 2) * ‖F c‖ ≤ Real.sqrt C * Real.sqrt (Real.pi * R ^ 2) := by
        calc (Real.pi * R ^ 2) * ‖F c‖
            = ‖(↑(Real.pi * R ^ 2) : ℂ) * F c‖ := by
              rw [norm_mul]
              simp
          _ = ‖∫ z in Metric.ball c R, F z‖ := by rw [hMV]
          _ ≤ ∫ z in Metric.ball c R, ‖F z‖ := h1
          _ ≤ Real.sqrt C * Real.sqrt (Real.pi * R ^ 2) := hcs
      have ha : 0 < Real.pi * R ^ 2 := by positivity
      have hsq : ((Real.pi * R ^ 2) * ‖F c‖) * ((Real.pi * R ^ 2) * ‖F c‖)
          ≤ (Real.sqrt C * Real.sqrt (Real.pi * R ^ 2))
              * (Real.sqrt C * Real.sqrt (Real.pi * R ^ 2)) :=
        mul_self_le_mul_self (by positivity) hle
      have hsC : Real.sqrt C * Real.sqrt C = C := by
        rw [← sq]; exact Real.sq_sqrt hCnn
      have hsa : Real.sqrt (Real.pi * R ^ 2) * Real.sqrt (Real.pi * R ^ 2)
          = Real.pi * R ^ 2 := by
        rw [← sq]; exact Real.sq_sqrt (by positivity)
      have hmain : (Real.pi * R ^ 2) * ‖F c‖ ^ 2 ≤ C := by
        have h2 : (Real.pi * R ^ 2) * ((Real.pi * R ^ 2) * ‖F c‖ ^ 2)
            ≤ (Real.pi * R ^ 2) * C := by
          calc (Real.pi * R ^ 2) * ((Real.pi * R ^ 2) * ‖F c‖ ^ 2)
              = ((Real.pi * R ^ 2) * ‖F c‖) * ((Real.pi * R ^ 2) * ‖F c‖) := by ring
            _ ≤ (Real.sqrt C * Real.sqrt (Real.pi * R ^ 2))
                  * (Real.sqrt C * Real.sqrt (Real.pi * R ^ 2)) := hsq
            _ = (Real.sqrt C * Real.sqrt C)
                  * (Real.sqrt (Real.pi * R ^ 2) * Real.sqrt (Real.pi * R ^ 2)) := by ring
            _ = C * (Real.pi * R ^ 2) := by rw [hsC, hsa]
            _ = (Real.pi * R ^ 2) * C := by ring
        exact le_of_mul_le_mul_left h2 ha
      rw [le_div_iff₀ Real.pi_pos]
      nlinarith [hmain]
    set K : ℝ := (C / Real.pi) / ‖F c‖ ^ 2 with hKdef
    have hKnn : 0 ≤ K := by
      rw [hKdef]; exact div_nonneg (div_nonneg hCnn Real.pi_pos.le) htpos.le
    have hKt : ‖F c‖ ^ 2 * K = C / Real.pi := by
      rw [hKdef, mul_comm]; exact div_mul_cancel₀ _ (ne_of_gt htpos)
    have hstep := hineq (K + 1) (by linarith)
    have hle2 : (K + 1) ^ 2 ≤ K := by
      have h2' : ‖F c‖ ^ 2 * (K + 1) ^ 2 ≤ ‖F c‖ ^ 2 * K := by rw [hKt]; exact hstep
      exact le_of_mul_le_mul_left h2' htpos
    nlinarith [hle2, hKnn, sq_nonneg K]
  have hnorm : ‖F c‖ = 0 := (pow_eq_zero_iff (n := 2) (by norm_num)).mp ht
  exact norm_eq_zero.mp hnorm

end

end Work.MRMT.Found
