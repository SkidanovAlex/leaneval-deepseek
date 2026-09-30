import Mathlib
import Submission.Commons.Analysis.Convolution.ball_tent_conv_lipschitz

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Commons.Analysis.Convolution

open MeasureTheory Metric
open scoped ENNReal

noncomputable section

private lemma one_add_max_zero_sub_one (t : ℝ) : 1 + max 0 (t - 1) = max 1 t := by
  by_cases h : 1 ≤ t
  · rw [max_eq_right (by linarith : 0 ≤ t - 1), max_eq_right h]; ring
  · rw [max_eq_left (by linarith : t - 1 ≤ 0), add_zero, max_eq_left (by linarith)]

private lemma max_zero_div (a b : ℝ) (hb : 0 < b) : max 0 a / b = max 0 (a / b) := by
  rw [← max_div_div_right hb.le (0 : ℝ) a, zero_div]

private lemma max_zero_sub_div (a : ℝ) {b : ℝ} (hb : 0 < b) :
    max 0 (a - b) / b = max 0 (a / b - 1) := by
  rw [max_zero_div _ _ hb, show (a - b) / b = a / b - 1 by rw [sub_div, div_self hb.ne']]

private lemma le_infDist_ball_zero {E : Type*} [NormedAddCommGroup E] {R : ℝ} (hR : 0 < R)
    (w : E) : max 0 (‖w‖ - R) ≤ Metric.infDist w (Metric.ball (0 : E) R) := by
  have hne : (Metric.ball (0 : E) R).Nonempty := ⟨0, by simp [Metric.mem_ball, hR]⟩
  refine max_le Metric.infDist_nonneg ?_
  rw [Metric.le_infDist hne]
  intro y hy
  rw [Metric.mem_ball, dist_zero_right] at hy
  rw [dist_eq_norm]
  have h : ‖w‖ ≤ ‖w - y‖ + ‖y‖ := by
    calc ‖w‖ = ‖(w - y) + y‖ := by rw [sub_add_cancel]
      _ ≤ ‖w - y‖ + ‖y‖ := norm_add_le _ _
  linarith

private lemma max_one_div_le_one_add_infDist {E : Type*} [NormedAddCommGroup E] {R : ℝ}
    (hR : 0 < R) (w : E) :
    max 1 (‖w‖ / R) ≤ 1 + Metric.infDist w (Metric.ball (0 : E) R) / R := by
  have h := le_infDist_ball_zero (E := E) hR w
  have h2 : max 0 (‖w‖ - R) / R ≤ Metric.infDist w (Metric.ball (0 : E) R) / R :=
    div_le_div_of_nonneg_right h hR.le
  rw [max_zero_sub_div (‖w‖) hR] at h2
  calc max 1 (‖w‖ / R) = 1 + max 0 (‖w‖ / R - 1) := (one_add_max_zero_sub_one _).symm
    _ ≤ 1 + Metric.infDist w (Metric.ball (0 : E) R) / R := by linarith

private lemma max_one_div_rpow_neg (y R A' : ℝ) (hR : 0 < R) (hy : 0 < y) :
    (max 1 (y / R)) ^ (-A') = R ^ A' * (max R y) ^ (-A') := by
  by_cases h : R ≤ y
  · rw [max_eq_right ((one_le_div hR).mpr h), max_eq_right h, div_eq_mul_inv,
      Real.mul_rpow hy.le (inv_nonneg.mpr hR.le), Real.inv_rpow hR.le, Real.rpow_neg hR.le A',
      inv_inv]
    ring
  · rw [max_eq_left (le_of_lt ((div_lt_one hR).mpr (lt_of_not_ge h))), Real.one_rpow,
      max_eq_left (le_of_lt (lt_of_not_ge h)), ← Real.rpow_add hR, add_neg_cancel,
      Real.rpow_zero]

theorem ball_tent_lintegral_le (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Nontrivial E]
    (A A' : ℝ) (hA : 0 < A) (hA' : A + (Module.finrank ℝ E : ℝ) < A') (C₀ : ℝ)
    (hC₀ : 1 ≤ C₀) :
    ∃ C : ℝ, 0 < C ∧ ∀ (R G : ℝ), 0 < R → 0 ≤ G →
      (MeasureTheory.lintegral (MeasureTheory.volume : MeasureTheory.Measure E)
        (fun w : E => ENNReal.ofReal
          (((MeasureTheory.volume (Metric.ball (0 : E) R)).toReal)⁻¹
            * (1 + Metric.infDist w (Metric.ball (0 : E) R) / R) ^ (-A')
            * (max 1 (G - C₀ * ‖w‖ / R)) ^ (-A))))
        ≤ ENNReal.ofReal C * ENNReal.ofReal ((max 1 G) ^ (-A)) := by
  obtain ⟨C, hCpos, hCbdd⟩ :=
    ball_tent_conv_lipschitz E A A' hA hA' C₀ hC₀
  refine ⟨C, hCpos, ?_⟩
  intro R G hR hG
  have hk : 1 ≤ Module.finrank ℝ E := Module.finrank_pos
  have hA'k : ((Module.finrank ℝ E : ℕ) : ℝ) < A' := by
    have : (0 : ℝ) < (Module.finrank ℝ E : ℝ) := by exact_mod_cast hk
    linarith
  set cR : ℝ := ((MeasureTheory.volume (Metric.ball (0 : E) R)).toReal)⁻¹ with hcR
  set ψ : ℝ → ℝ := fun y => cR * (max 1 (y / R)) ^ (-A') with hψ
  have hcRnn : 0 ≤ cR := by rw [hcR]; exact inv_nonneg.mpr ENNReal.toReal_nonneg
  -- integrability of `ψ ‖·‖`
  have hIntψ : IntegrableOn (fun y : ℝ => y ^ (Module.finrank ℝ E - 1) * ψ y) (Set.Ioi 0) := by
    rw [← Set.Ioc_union_Ioi_eq_Ioi (le_of_lt hR), integrableOn_union]
    refine ⟨?_, ?_⟩
    · have hcont : ContinuousOn (fun y : ℝ => y ^ (Module.finrank ℝ E - 1) * cR)
          (Set.Icc 0 R) := ((continuous_pow _).continuousOn).mul continuousOn_const
      have hIcc : IntegrableOn (fun y : ℝ => y ^ (Module.finrank ℝ E - 1) * cR)
          (Set.Icc 0 R) := hcont.integrableOn_Icc
      refine (hIcc.mono_set Set.Ioc_subset_Icc_self).congr_fun ?_ measurableSet_Ioc
      intro y hy
      simp only [hψ]
      rw [max_eq_left ((div_le_one hR).mpr hy.2), Real.one_rpow, mul_one]
    · have hlt : (((Module.finrank ℝ E : ℕ) : ℝ) - 1) - A' < -1 := by linarith [hA'k]
      have hbase : IntegrableOn (fun y : ℝ => y ^ ((((Module.finrank ℝ E : ℕ) : ℝ)) - 1 - A'))
          (Set.Ioi R) := integrableOn_Ioi_rpow_of_lt hlt hR
      have hbase2 : IntegrableOn
          (fun y : ℝ => (cR * R ^ A') * y ^ ((((Module.finrank ℝ E : ℕ) : ℝ)) - 1 - A'))
          (Set.Ioi R) := hbase.const_mul (cR * R ^ A')
      refine hbase2.congr_fun ?_ measurableSet_Ioi
      intro y hy
      have hy0 : 0 < y := lt_trans hR hy
      simp only [hψ]
      rw [max_one_div_rpow_neg y R A' hR hy0, max_eq_right (le_of_lt hy),
        ← Real.rpow_natCast y (Module.finrank ℝ E - 1)]
      rw [show y ^ (((Module.finrank ℝ E - 1 : ℕ) : ℝ)) * (cR * (R ^ A' * y ^ (-A')))
            = cR * R ^ A' * (y ^ (((Module.finrank ℝ E - 1 : ℕ) : ℝ)) * y ^ (-A'))
            by ring_nf]
      rw [← Real.rpow_add hy0]
      congr 1
      rw [Nat.cast_sub hk, Nat.cast_one]; ring
  have hintg : Integrable (fun w : E => ψ ‖w‖) (MeasureTheory.volume : MeasureTheory.Measure E) :=
    (MeasureTheory.integrable_fun_norm_addHaar (MeasureTheory.volume : MeasureTheory.Measure E)
      (f := ψ)).mpr hIntψ
  -- continuity / measurability of the integrand
  have hbase1 : ∀ w : E, 1 ≤ 1 + Metric.infDist w (Metric.ball (0 : E) R) / R := fun w =>
    le_add_of_nonneg_right (div_nonneg Metric.infDist_nonneg hR.le)
  have hcont1 : Continuous (fun w : E => (1 + Metric.infDist w (Metric.ball (0 : E) R) / R)) :=
    (continuous_const : Continuous (fun _ : E => (1 : ℝ))).add
      ((Metric.continuous_infDist_pt (Metric.ball (0 : E) R)).div_const R)
  have hcont1p : Continuous
      (fun w : E => (1 + Metric.infDist w (Metric.ball (0 : E) R) / R) ^ (-A')) :=
    hcont1.rpow_const (fun w => Or.inl (ne_of_gt (lt_of_lt_of_le zero_lt_one (hbase1 w))))
  have hcont2 : Continuous (fun w : E => max 1 (G - C₀ * ‖w‖ / R)) :=
    (continuous_const : Continuous (fun _ : E => (1 : ℝ))).max
      ((continuous_const : Continuous (fun _ : E => G)).sub
        (((continuous_const : Continuous (fun _ : E => C₀)).mul continuous_norm).div_const R))
  have hcont2p : Continuous (fun w : E => (max 1 (G - C₀ * ‖w‖ / R)) ^ (-A)) :=
    hcont2.rpow_const
      (fun w => Or.inl (ne_of_gt (lt_of_lt_of_le zero_lt_one (le_max_left _ _))))
  have hΦcont : Continuous (fun w : E =>
      cR * (1 + Metric.infDist w (Metric.ball (0 : E) R) / R) ^ (-A')
        * (max 1 (G - C₀ * ‖w‖ / R)) ^ (-A)) :=
    ((continuous_const : Continuous (fun _ : E => cR)).mul hcont1p).mul hcont2p
  -- domination by `ψ ‖·‖`
  have hle : ∀ w : E,
      ‖cR * (1 + Metric.infDist w (Metric.ball (0 : E) R) / R) ^ (-A')
        * (max 1 (G - C₀ * ‖w‖ / R)) ^ (-A)‖ ≤ ψ ‖w‖ := by
    intro w
    have h1nn : 0 ≤ (1 + Metric.infDist w (Metric.ball (0 : E) R) / R) ^ (-A') :=
      Real.rpow_nonneg (le_trans zero_le_one (hbase1 w)) _
    have h2nn : 0 ≤ (max 1 (G - C₀ * ‖w‖ / R)) ^ (-A) :=
      Real.rpow_nonneg (le_trans zero_le_one (le_max_left _ _)) _
    rw [Real.norm_of_nonneg (mul_nonneg (mul_nonneg hcRnn h1nn) h2nn)]
    simp only [hψ]
    have hA2le1 : (max 1 (G - C₀ * ‖w‖ / R)) ^ (-A) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (le_max_left _ _) (by linarith : -A ≤ 0)
    have hBpos : 0 < max 1 (‖w‖ / R) := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
    have hA1leB : (1 + Metric.infDist w (Metric.ball (0 : E) R) / R) ^ (-A')
        ≤ (max 1 (‖w‖ / R)) ^ (-A') :=
      Real.rpow_le_rpow_of_nonpos hBpos (max_one_div_le_one_add_infDist hR w)
        (by linarith : -A' ≤ 0)
    have hBnn : 0 ≤ (max 1 (‖w‖ / R)) ^ (-A') :=
      Real.rpow_nonneg (le_trans zero_le_one (le_max_left _ _)) _
    calc cR * (1 + Metric.infDist w (Metric.ball (0 : E) R) / R) ^ (-A')
          * (max 1 (G - C₀ * ‖w‖ / R)) ^ (-A)
        = cR * ((1 + Metric.infDist w (Metric.ball (0 : E) R) / R) ^ (-A')
            * (max 1 (G - C₀ * ‖w‖ / R)) ^ (-A)) := by ring
      _ ≤ cR * ((max 1 (‖w‖ / R)) ^ (-A') * 1) := by
          apply mul_le_mul_of_nonneg_left _ hcRnn
          exact mul_le_mul hA1leB hA2le1 h2nn hBnn
      _ = cR * (max 1 (‖w‖ / R)) ^ (-A') := by ring
  have hΦint : Integrable (fun w : E =>
      cR * (1 + Metric.infDist w (Metric.ball (0 : E) R) / R) ^ (-A')
        * (max 1 (G - C₀ * ‖w‖ / R)) ^ (-A)) (MeasureTheory.volume : MeasureTheory.Measure E) :=
    hintg.mono' hΦcont.aestronglyMeasurable (Filter.Eventually.of_forall hle)
  have hΦnn : ∀ w : E, 0 ≤ cR * (1 + Metric.infDist w (Metric.ball (0 : E) R) / R) ^ (-A')
        * (max 1 (G - C₀ * ‖w‖ / R)) ^ (-A) := by
    intro w
    exact mul_nonneg (mul_nonneg hcRnn (Real.rpow_nonneg (le_trans zero_le_one (hbase1 w)) _))
      (Real.rpow_nonneg (le_trans zero_le_one (le_max_left _ _)) _)
  rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal hΦint
    (Filter.Eventually.of_forall hΦnn)]
  have hb := hCbdd R G hR hG
  rw [← hcR] at hb
  rw [← ENNReal.ofReal_mul (le_of_lt hCpos)]
  exact ENNReal.ofReal_le_ofReal hb

end

end Commons.Analysis.Convolution
