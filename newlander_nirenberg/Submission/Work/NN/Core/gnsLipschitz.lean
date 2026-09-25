
import Mathlib
import Submission.Work.NN.Core.gagliardoNirenbergGeomMean
import Submission.Work.NN.Core.CnPert
import Submission.Work.NN.Core.eLpNorm_integral_smul_sub_le

noncomputable section

open MeasureTheory Filter Function
open scoped ENNReal NNReal ContDiff Convolution Topology Pointwise

namespace Work.NN.Core

/-! ## Auxiliary lemmas for `gnsLipschitz`

The Gagliardo–Nirenberg (geometric mean) inequality is available in the workspace for `C¹`
functions with compact support (`gagliardoNirenbergGeomMean`).  Here we extend it to Lipschitz
functions with compact support, by mollifying and passing to the limit.

The two ingredients are

* `fderiv_convolution_of_lipschitz_tmp`: the derivative of the mollification of a Lipschitz
  function is the mollification of its (a.e.) derivative.  The proof uses Rademacher's theorem
  (`LipschitzWith.ae_differentiableAt`), dominated convergence and the characterisation
  `hasFDerivAt_iff_tendsto` of the Fréchet derivative.  (The same statement is also proved,
  independently, in `Submission.Work.NN.Core.fderiv_convolution_of_lipschitz`.)
* `Work.NN.Core.eLpNorm_integral_smul_sub_le` (imported): convolving with a probability density
  does not increase the `L²` norm.

The final step takes `lim` along the mollifier family: the per-`m` Gagliardo–Nirenberg bound for
the smooth `Wm m` is compared with the `Lᵖ`-(semi)norms of `W` using
`tendsto_toReal_eLpNorm_of_uniform`.
-/

/-- The derivative of the mollification of a Lipschitz function is the mollification of its
(a.e.) derivative. -/
private theorem fderiv_convolution_of_lipschitz_tmp {n : ℕ} {L : NNReal} {W : Cn n → ℂ}
    (hLip : LipschitzWith L W) (hcs : HasCompactSupport W) {ρ : Cn n → ℝ}
    (hρ0 : ∀ t, 0 ≤ ρ t) (hρi : Integrable ρ volume) (x₀ : Cn n) :
    fderiv ℝ (fun y => ∫ t, ρ t • W (y - t) ∂volume) x₀ =
      ∫ t, ρ t • fderiv ℝ W (x₀ - t) ∂volume := by
  classical
  -- boundedness of `W` (compact support) and of `fderiv ℝ W` (Lipschitz)
  obtain ⟨CW₀, hCW₀⟩ := hLip.continuous.bounded_above_of_compact_support hcs
  have hCW : ∀ y, ‖W y‖ ≤ max CW₀ 0 := fun y => (hCW₀ y).trans (le_max_left _ _)
  have hdfd : ∀ y, ‖fderiv ℝ W y‖ ≤ (L : ℝ) := fun y => norm_fderiv_le_of_lipschitz ℝ hLip
  -- integrability of the two integrands of `x ↦ ∫ ρ t • W (x - t)` and of the target
  have hintW : ∀ y, Integrable (fun t : Cn n => ρ t • W (y - t)) volume := by
    intro y
    refine Integrable.mono' (hρi.mul_const (max CW₀ 0))
      (hρi.aestronglyMeasurable.smul
        ((hLip.continuous.comp (continuous_const.sub continuous_id)).aestronglyMeasurable))
      (Eventually.of_forall fun t => ?_)
    rw [norm_smul, Real.norm_of_nonneg (hρ0 t)]
    exact mul_le_mul_of_nonneg_left (hCW (y - t)) (hρ0 t)
  have hintdfd : Integrable (fun t : Cn n => ρ t • fderiv ℝ W (x₀ - t)) volume := by
    refine Integrable.mono' (hρi.mul_const (L : ℝ))
      (hρi.aestronglyMeasurable.smul
        ((measurable_fderiv ℝ W).comp
          (continuous_const.sub continuous_id).measurable).aestronglyMeasurable)
      (Eventually.of_forall fun t => ?_)
    rw [norm_smul, Real.norm_of_nonneg (hρ0 t)]
    exact mul_le_mul_of_nonneg_left (hdfd (x₀ - t)) (hρ0 t)
  -- a.e. differentiability (transferred along `y ↦ x₀ - y`)
  have hae : ∀ᵐ y ∂(volume : Measure (Cn n)), DifferentiableAt ℝ W (x₀ - y) :=
    (MeasureTheory.Measure.measurePreserving_sub_left volume x₀).quasiMeasurePreserving.ae
      hLip.ae_differentiableAt
  -- the integrable dominating function
  have hbound_int : Integrable (fun y : Cn n => (2 * (L : ℝ)) * ρ y) volume :=
    hρi.const_mul (2 * (L : ℝ))
  -- dominated convergence
  have hdct : Tendsto (fun x' : Cn n => ∫ y, ρ y * (‖x' - x₀‖⁻¹ *
      ‖W (x' - y) - W (x₀ - y) - fderiv ℝ W (x₀ - y) (x' - x₀)‖) ∂volume)
      (𝓝 x₀) (𝓝 0) := by
    have h := MeasureTheory.tendsto_integral_filter_of_dominated_convergence
      (μ := volume) (l := 𝓝 x₀)
      (F := fun x' y => ρ y * (‖x' - x₀‖⁻¹ *
        ‖W (x' - y) - W (x₀ - y) - fderiv ℝ W (x₀ - y) (x' - x₀)‖))
      (f := fun _ => 0) (fun y => (2 * (L : ℝ)) * ρ y) ?_ ?_ hbound_int ?_
    · simpa using h
    · -- measurability
      filter_upwards with x'
      refine hρi.aestronglyMeasurable.mul ?_
      have hm : Measurable (fun y : Cn n =>
          ‖W (x' - y) - W (x₀ - y) - fderiv ℝ W (x₀ - y) (x' - x₀)‖) := by
        refine Measurable.norm (Measurable.sub (Measurable.sub ?_ ?_) ?_)
        · exact (hLip.continuous.comp (continuous_const.sub continuous_id)).measurable
        · exact (hLip.continuous.comp (continuous_const.sub continuous_id)).measurable
        · exact ((measurable_fderiv_apply_const ℝ W (x' - x₀)).comp
            (continuous_const.sub continuous_id).measurable)
      exact (hm.const_mul _).aestronglyMeasurable
    · -- domination
      filter_upwards with x'
      filter_upwards with y
      have hb : ‖W (x' - y) - W (x₀ - y) - fderiv ℝ W (x₀ - y) (x' - x₀)‖
          ≤ 2 * (L : ℝ) * ‖x' - x₀‖ := by
        have h1 : ‖W (x' - y) - W (x₀ - y)‖ ≤ (L : ℝ) * ‖(x' - y) - (x₀ - y)‖ :=
          hLip.norm_sub_le _ _
        have h2 : ‖fderiv ℝ W (x₀ - y) (x' - x₀)‖ ≤ (L : ℝ) * ‖x' - x₀‖ :=
          (ContinuousLinearMap.le_opNorm _ _).trans
            (mul_le_mul_of_nonneg_right (hdfd _) (norm_nonneg _))
        have h3 : (x' - y) - (x₀ - y) = x' - x₀ := by abel
        rw [h3] at h1
        calc ‖W (x' - y) - W (x₀ - y) - fderiv ℝ W (x₀ - y) (x' - x₀)‖
            ≤ ‖W (x' - y) - W (x₀ - y)‖ + ‖fderiv ℝ W (x₀ - y) (x' - x₀)‖ := norm_sub_le _ _
          _ ≤ (L : ℝ) * ‖x' - x₀‖ + (L : ℝ) * ‖x' - x₀‖ := add_le_add h1 h2
          _ = 2 * (L : ℝ) * ‖x' - x₀‖ := by ring
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hρ0 y) (mul_nonneg (by positivity)
        (norm_nonneg _)))]
      have hb' : ‖x' - x₀‖⁻¹ * ‖W (x' - y) - W (x₀ - y) - fderiv ℝ W (x₀ - y) (x' - x₀)‖
          ≤ 2 * (L : ℝ) := by
        rcases eq_or_ne x' x₀ with rfl | hx'
        · simp only [sub_self, norm_zero, inv_zero, zero_mul]
          exact mul_nonneg (by norm_num) L.coe_nonneg
        · have hnorm : ‖x' - x₀‖ ≠ 0 := norm_ne_zero_iff.mpr (sub_ne_zero.mpr hx')
          have hinv : ‖x' - x₀‖⁻¹ * ‖x' - x₀‖ = 1 := inv_mul_cancel₀ hnorm
          calc ‖x' - x₀‖⁻¹ * ‖W (x' - y) - W (x₀ - y) - fderiv ℝ W (x₀ - y) (x' - x₀)‖
              ≤ ‖x' - x₀‖⁻¹ * (2 * (L : ℝ) * ‖x' - x₀‖) :=
                mul_le_mul_of_nonneg_left hb (by positivity)
            _ = 2 * (L : ℝ) := by
                have h2 : ‖x' - x₀‖⁻¹ * (2 * (L : ℝ) * ‖x' - x₀‖)
                    = 2 * (L : ℝ) * (‖x' - x₀‖⁻¹ * ‖x' - x₀‖) := by ring
                rw [h2, hinv, mul_one]
      calc ρ y * (‖x' - x₀‖⁻¹ * ‖W (x' - y) - W (x₀ - y) - fderiv ℝ W (x₀ - y) (x' - x₀)‖)
          ≤ ρ y * (2 * (L : ℝ)) := mul_le_mul_of_nonneg_left hb' (hρ0 y)
        _ = 2 * (L : ℝ) * ρ y := by ring
    · -- a.e. convergence
      filter_upwards [hae] with y hy
      have hdiff : HasFDerivAt W (fderiv ℝ W (x₀ - y)) (x₀ - y) := hy.hasFDerivAt
      have hcomp := (hasFDerivAt_iff_tendsto.mp hdiff).comp
        (tendsto_id.sub_const y)
      have hlim : Tendsto (fun x' : Cn n => ‖x' - x₀‖⁻¹ *
          ‖W (x' - y) - W (x₀ - y) - fderiv ℝ W (x₀ - y) (x' - x₀)‖) (𝓝 x₀) (𝓝 0) := by
        refine hcomp.congr' (Eventually.of_forall fun x' => ?_)
        show ‖(x' - y) - (x₀ - y)‖⁻¹ * ‖W (x' - y) - W (x₀ - y)
              - fderiv ℝ W (x₀ - y) ((x' - y) - (x₀ - y))‖
            = ‖x' - x₀‖⁻¹ * ‖W (x' - y) - W (x₀ - y) - fderiv ℝ W (x₀ - y) (x' - x₀)‖
        rw [show (x' - y) - (x₀ - y) = x' - x₀ from by abel]
      simpa using ((tendsto_const_nhds : Tendsto (fun _ : Cn n => ρ y) (𝓝 x₀) (𝓝 (ρ y))).mul
        hlim)
  -- the linearity identity
  have hlin : ∀ x' : Cn n,
      (∫ t, ρ t • W (x' - t) ∂volume) - (∫ t, ρ t • W (x₀ - t) ∂volume)
        - (∫ t, ρ t • fderiv ℝ W (x₀ - t) ∂volume) (x' - x₀)
      = ∫ t, ρ t • (W (x' - t) - W (x₀ - t) - fderiv ℝ W (x₀ - t) (x' - x₀)) ∂volume := by
    intro x'
    have hCsmul : Integrable (fun t : Cn n => ρ t • (fderiv ℝ W (x₀ - t) (x' - x₀))) volume := by
      refine Integrable.mono' (hρi.mul_const ((L : ℝ) * ‖x' - x₀‖))
        (hρi.aestronglyMeasurable.smul (((measurable_fderiv_apply_const ℝ W (x' - x₀)).comp
          (continuous_const.sub continuous_id).measurable)).aestronglyMeasurable)
        (Eventually.of_forall fun t => ?_)
      rw [norm_smul, Real.norm_of_nonneg (hρ0 t)]
      refine mul_le_mul_of_nonneg_left ?_ (hρ0 t)
      exact (ContinuousLinearMap.le_opNorm _ _).trans
        (mul_le_mul_of_nonneg_right (hdfd _) (norm_nonneg _))
    have hC : Integrable (fun t : Cn n => (ρ t • fderiv ℝ W (x₀ - t)) (x' - x₀)) volume :=
      hCsmul.congr (Eventually.of_forall fun t => by simp only [ContinuousLinearMap.smul_apply])
    have hsplit3 : (∫ t, ρ t • fderiv ℝ W (x₀ - t) ∂volume) (x' - x₀)
        = ∫ t, (ρ t • fderiv ℝ W (x₀ - t)) (x' - x₀) ∂volume :=
      ContinuousLinearMap.integral_apply hintdfd (x' - x₀)
    have hsplit : (∫ t, ρ t • W (x' - t) ∂volume) - (∫ t, ρ t • W (x₀ - t) ∂volume)
        = ∫ t, (ρ t • W (x' - t) - ρ t • W (x₀ - t)) ∂volume :=
      (integral_sub (hintW x') (hintW x₀)).symm
    have hsplit2 : (∫ t, (ρ t • W (x' - t) - ρ t • W (x₀ - t)) ∂volume)
        - (∫ t, (ρ t • fderiv ℝ W (x₀ - t)) (x' - x₀) ∂volume)
        = ∫ t, ((ρ t • W (x' - t) - ρ t • W (x₀ - t))
            - (ρ t • fderiv ℝ W (x₀ - t)) (x' - x₀)) ∂volume :=
      (integral_sub ((hintW x').sub (hintW x₀)) hC).symm
    rw [hsplit3, hsplit, hsplit2]
    refine integral_congr_ae (Eventually.of_forall fun t => ?_)
    simp only [smul_sub, ContinuousLinearMap.smul_apply]
    try abel
  -- the main convergence statement
  have hmain : Tendsto (fun x' => ‖x' - x₀‖⁻¹ * ‖(∫ t, ρ t • W (x' - t) ∂volume)
      - (∫ t, ρ t • W (x₀ - t) ∂volume)
      - (∫ t, ρ t • fderiv ℝ W (x₀ - t) ∂volume) (x' - x₀)‖) (𝓝 x₀) (𝓝 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hdct (fun x' => ?_) (fun x' => ?_)
    · positivity
    · rw [hlin x']
      calc ‖x' - x₀‖⁻¹ * ‖∫ y, ρ y • (W (x' - y) - W (x₀ - y)
            - fderiv ℝ W (x₀ - y) (x' - x₀)) ∂volume‖
          ≤ ‖x' - x₀‖⁻¹ * ∫ y, ‖ρ y • (W (x' - y) - W (x₀ - y)
              - fderiv ℝ W (x₀ - y) (x' - x₀))‖ ∂volume :=
            mul_le_mul_of_nonneg_left (norm_integral_le_integral_norm _) (by positivity)
        _ = ‖x' - x₀‖⁻¹ * ∫ y, ρ y * ‖W (x' - y) - W (x₀ - y)
              - fderiv ℝ W (x₀ - y) (x' - x₀)‖ ∂volume := by
            congr 1
            congr 1
            ext y
            rw [norm_smul, Real.norm_of_nonneg (hρ0 y)]
        _ = ∫ y, ρ y * (‖x' - x₀‖⁻¹ * ‖W (x' - y) - W (x₀ - y)
              - fderiv ℝ W (x₀ - y) (x' - x₀)‖) ∂volume := by
            rw [← integral_const_mul]
            congr 1
            ext y
            ring
  have hfd : HasFDerivAt (fun y => ∫ t, ρ t • W (y - t) ∂volume)
      (∫ t, ρ t • fderiv ℝ W (x₀ - t) ∂volume) x₀ :=
    hasFDerivAt_iff_tendsto.mpr hmain
  exact hfd.fderiv

/-- A function supported in a compact set `K` and bounded there by the extended nonnegative real
number `C` has `Lᵖ` norm at most `C · (volume K)^{1/p}`. -/
lemma eLpNorm_le_of_support_subset_isCompact {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {n : ℕ} {p : ℝ≥0∞} {f : Cn n → F} {K : Set (Cn n)} {C : ℝ≥0∞}
    (hp0 : p ≠ 0) (hptop : p ≠ ⊤) (hK : IsCompact K) (hmeas : AEStronglyMeasurable f volume)
    (hbdd : ∀ x ∈ K, ‖f x‖ₑ ≤ C) (hsupp : ∀ x ∉ K, f x = 0) :
    eLpNorm f p volume ≤ C * (volume K) ^ (1 / p.toReal) := by
  have hp : 0 < p.toReal := ENNReal.toReal_pos hp0 hptop
  have hae : f =ᵐ[volume] K.indicator f := by
    filter_upwards with x
    by_cases hx : x ∈ K
    · rw [Set.indicator_of_mem hx]
    · rw [Set.indicator_of_notMem hx, hsupp x hx]
  have hmeas' : AEStronglyMeasurable (K.indicator f) volume := hmeas.indicator hK.measurableSet
  have hpt : ∀ᵐ x ∂(volume : Measure (Cn n)),
      ‖K.indicator f x‖ₑ ^ p.toReal ≤ (K.indicator (fun _ => C) x) ^ p.toReal := by
    filter_upwards with x
    by_cases hx : x ∈ K
    · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx]
      exact ENNReal.rpow_le_rpow (hbdd x hx) hp.le
    · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx, enorm_zero,
        ENNReal.zero_rpow_of_pos hp]
  calc eLpNorm f p volume = eLpNorm (K.indicator f) p volume := eLpNorm_congr_ae hae
    _ = (∫⁻ x, ‖K.indicator f x‖ₑ ^ p.toReal ∂volume) ^ (1 / p.toReal) :=
        eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hptop hmeas'
    _ ≤ (∫⁻ x, (K.indicator (fun _ => C) x) ^ p.toReal ∂volume) ^ (1 / p.toReal) :=
        ENNReal.rpow_le_rpow (lintegral_mono_ae hpt) (by positivity)
    _ = (∫⁻ x, K.indicator (fun _ => C ^ p.toReal) x ∂volume) ^ (1 / p.toReal) := by
        congr 1
        refine lintegral_congr fun x => ?_
        by_cases hx : x ∈ K
        · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx]
        · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx,
            ENNReal.zero_rpow_of_pos hp]
    _ = (C ^ p.toReal * volume K) ^ (1 / p.toReal) := by
        rw [lintegral_indicator_const hK.measurableSet]
    _ = C * (volume K) ^ (1 / p.toReal) := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ (by positivity), ← ENNReal.rpow_mul,
          mul_one_div_cancel hp.ne', ENNReal.rpow_one]

/-- Uniform bound on the `Lᵖ` norm of the difference of a uniformly convergent sequence supported
in a fixed compact set. -/
lemma eLpNorm_sub_le_of_uniform_bound {n : ℕ} {p : ℝ≥0∞} (hp1 : 1 ≤ p) (hptop : p ≠ ⊤)
    {W : Cn n → ℂ} {Wm : ℕ → Cn n → ℂ} {K : Set (Cn n)} (hK : IsCompact K)
    (hKsub : ∀ m, Function.support (fun x => Wm m x - W x) ⊆ K)
    (hmeas : ∀ m, AEStronglyMeasurable (fun x => Wm m x - W x) volume)
    {c : ℕ → ℝ} (hc0 : ∀ m, 0 ≤ c m) (hbdd : ∀ m x, ‖Wm m x - W x‖ ≤ c m) (m : ℕ) :
    eLpNorm (fun x => Wm m x - W x) p volume
      ≤ ENNReal.ofReal (c m * (volume K).toReal ^ (1 / p.toReal)) := by
  have hp0 : p ≠ 0 := fun h => by rw [h] at hp1; exact absurd hp1 (by norm_num)
  have hKfin : (volume K) ≠ ⊤ := hK.measure_lt_top.ne
  have hpow : (volume K) ^ (1 / p.toReal)
      = ENNReal.ofReal ((volume K).toReal ^ (1 / p.toReal)) := by
    conv_lhs => rw [← ENNReal.ofReal_toReal hKfin]
    rw [ENNReal.ofReal_rpow_of_nonneg ENNReal.toReal_nonneg
      (div_nonneg zero_le_one ENNReal.toReal_nonneg)]
  have h := eLpNorm_le_of_support_subset_isCompact (p := p) (f := fun x => Wm m x - W x)
    (K := K) (C := ENNReal.ofReal (c m)) hp0 hptop hK (hmeas m)
    (fun x _ => by rw [← ofReal_norm]; exact ENNReal.ofReal_le_ofReal (hbdd m x))
    (fun x hx => by
      by_contra hne
      exact hx (hKsub m (Function.mem_support.mpr hne)))
  rwa [hpow, ← ENNReal.ofReal_mul (hc0 m)] at h

/-- The `Lᵖ` distance of a uniformly convergent sequence (supported in a fixed compact set) to its
limit tends to `0`. -/
lemma tendsto_toReal_eLpNorm_sub_of_uniform {n : ℕ} {p : ℝ≥0∞} (hp1 : 1 ≤ p) (hptop : p ≠ ⊤)
    {W : Cn n → ℂ} {Wm : ℕ → Cn n → ℂ} {K : Set (Cn n)} (hK : IsCompact K)
    (hKsub : ∀ m, Function.support (fun x => Wm m x - W x) ⊆ K)
    (hmeas : ∀ m, AEStronglyMeasurable (fun x => Wm m x - W x) volume)
    {c : ℕ → ℝ} (hc0 : ∀ m, 0 ≤ c m) (hc : Tendsto c atTop (nhds 0))
    (hbdd : ∀ m x, ‖Wm m x - W x‖ ≤ c m) :
    Tendsto (fun m => (eLpNorm (fun x => Wm m x - W x) p volume).toReal) atTop (nhds 0) := by
  have hboundR : ∀ m, (eLpNorm (fun x => Wm m x - W x) p volume).toReal
      ≤ c m * (volume K).toReal ^ (1 / p.toReal) := by
    intro m
    have := ENNReal.toReal_mono (ENNReal.ofReal_ne_top)
      (eLpNorm_sub_le_of_uniform_bound hp1 hptop hK hKsub hmeas hc0 hbdd m)
    rwa [ENNReal.toReal_ofReal (mul_nonneg (hc0 m) (by positivity))] at this
  have hlimR : Tendsto (fun m => c m * (volume K).toReal ^ (1 / p.toReal)) atTop (nhds 0) := by
    have h := hc.mul_const ((volume K).toReal ^ (1 / p.toReal))
    simpa using h
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlimR
    (fun m => by positivity) hboundR

/-- **Limit of `Lᵖ` norms along a uniformly convergent sequence supported in a fixed compact set.**
If `‖Wm m x - W x‖ ≤ c m` with `c m → 0` and the differences are supported in a fixed compact
set `K`, then `(eLpNorm (Wm m) p).toReal → (eLpNorm W p).toReal`, and the `Lᵖ` distance to the
limit tends to `0`. -/
lemma tendsto_toReal_eLpNorm_of_uniform {n : ℕ} {p : ℝ≥0∞} (hp1 : 1 ≤ p) (hptop : p ≠ ⊤)
    {W : Cn n → ℂ} {Wm : ℕ → Cn n → ℂ} {K : Set (Cn n)} (hK : IsCompact K)
    (hKsub : ∀ m, Function.support (fun x => Wm m x - W x) ⊆ K)
    (hmeas : ∀ m, AEStronglyMeasurable (fun x => Wm m x - W x) volume)
    (hWfin : eLpNorm W p volume ≠ ⊤) (hWmfin : ∀ m, eLpNorm (Wm m) p volume ≠ ⊤)
    {c : ℕ → ℝ} (hc0 : ∀ m, 0 ≤ c m) (hc : Tendsto c atTop (nhds 0))
    (hbdd : ∀ m x, ‖Wm m x - W x‖ ≤ c m) :
    Tendsto (fun m => (eLpNorm (Wm m) p volume).toReal) atTop
        (nhds ((eLpNorm W p volume).toReal)) ∧
      Tendsto (fun m => (eLpNorm (fun x => Wm m x - W x) p volume).toReal) atTop (nhds 0) := by
  have hdiffne : ∀ m, eLpNorm (fun x => Wm m x - W x) p volume ≠ ⊤ := by
    intro m
    exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top
      (eLpNorm_sub_le_of_uniform_bound hp1 hptop hK hKsub hmeas hc0 hbdd m)
  have hem := tendsto_toReal_eLpNorm_sub_of_uniform hp1 hptop hK hKsub hmeas hc0 hc hbdd
  have hle1 : ∀ m, (eLpNorm W p volume).toReal
      ≤ (eLpNorm (Wm m) p volume).toReal
        + (eLpNorm (fun x => Wm m x - W x) p volume).toReal := by
    intro m
    have h1 : eLpNorm W p volume ≤ eLpNorm (Wm m) p volume
        + eLpNorm (fun x => Wm m x - W x) p volume := by
      have h := eLpNorm_add_le (μ := volume) (p := p)
        (f := Wm m) (g := fun x => W x - Wm m x) hp1
      have h2 : Wm m + (fun x => W x - Wm m x) = W := by
        funext x; simp only [Pi.add_apply]; abel
      have h3 : eLpNorm (fun x => W x - Wm m x) p volume
          = eLpNorm (fun x => Wm m x - W x) p volume := by
        have h4 : (fun x => W x - Wm m x) = -(fun x => Wm m x - W x) := by
          funext x; simp only [Pi.neg_apply]; abel
        rw [h4, eLpNorm_neg]
      rwa [h2, h3] at h
    calc (eLpNorm W p volume).toReal
        ≤ (eLpNorm (Wm m) p volume
            + eLpNorm (fun x => Wm m x - W x) p volume).toReal :=
          ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨hWmfin m, hdiffne m⟩) h1
      _ = (eLpNorm (Wm m) p volume).toReal
            + (eLpNorm (fun x => Wm m x - W x) p volume).toReal :=
          ENNReal.toReal_add (hWmfin m) (hdiffne m)
  have hle2 : ∀ m, (eLpNorm (Wm m) p volume).toReal
      ≤ (eLpNorm W p volume).toReal
        + (eLpNorm (fun x => Wm m x - W x) p volume).toReal := by
    intro m
    have h1 : eLpNorm (Wm m) p volume ≤ eLpNorm W p volume
        + eLpNorm (fun x => Wm m x - W x) p volume := by
      have h := eLpNorm_add_le (μ := volume) (p := p)
        (f := W) (g := fun x => Wm m x - W x) hp1
      have h2 : W + (fun x => Wm m x - W x) = Wm m := by
        funext x; simp only [Pi.add_apply]; abel
      rwa [h2] at h
    calc (eLpNorm (Wm m) p volume).toReal
        ≤ (eLpNorm W p volume
            + eLpNorm (fun x => Wm m x - W x) p volume).toReal :=
          ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨hWfin, hdiffne m⟩) h1
      _ = (eLpNorm W p volume).toReal
            + (eLpNorm (fun x => Wm m x - W x) p volume).toReal :=
          ENNReal.toReal_add hWfin (hdiffne m)
  have hup : Tendsto (fun m => (eLpNorm W p volume).toReal
      + (eLpNorm (fun x => Wm m x - W x) p volume).toReal) atTop
      (nhds ((eLpNorm W p volume).toReal)) := by
    have h : Tendsto (fun m => (eLpNorm W p volume).toReal
        + (eLpNorm (fun x => Wm m x - W x) p volume).toReal) atTop
        (nhds ((eLpNorm W p volume).toReal + 0)) := tendsto_const_nhds.add hem
    simpa using h
  have hdown : Tendsto (fun m => (eLpNorm W p volume).toReal
      - (eLpNorm (fun x => Wm m x - W x) p volume).toReal) atTop
      (nhds ((eLpNorm W p volume).toReal)) := by
    have h : Tendsto (fun m => (eLpNorm W p volume).toReal
        - (eLpNorm (fun x => Wm m x - W x) p volume).toReal) atTop
        (nhds ((eLpNorm W p volume).toReal - 0)) := tendsto_const_nhds.sub hem
    simpa using h
  have hmain : Tendsto (fun m => (eLpNorm (Wm m) p volume).toReal) atTop
      (nhds ((eLpNorm W p volume).toReal)) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le hdown hup
      (fun m => by have := hle1 m; linarith)
      (fun m => by have := hle2 m; linarith)
  exact ⟨hmain, hem⟩

/-- The radius family `δ m = min (1/(m+1)) 1` tends to `0`. -/
lemma tendsto_min_one_div_add_one_one :
    Tendsto (fun m : ℕ => min (1 / ((m : ℝ) + 1)) 1) atTop (nhds 0) := by
  have h1 : Tendsto (fun m : ℕ => 1 / ((m : ℝ) + 1)) atTop (nhds 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
  have h2 : Tendsto (fun m : ℕ => min (1 / ((m : ℝ) + 1)) (1 : ℝ)) atTop (nhds (min 0 1)) :=
    h1.min tendsto_const_nhds
  simpa using h2

/-- Existence of a mollifier family on `ℂⁿ` with supports shrinking to `{0}`. -/
lemma exists_mollifier_family_Cn (n : ℕ) :
    ∃ (δ : ℕ → ℝ) (φ : ℕ → Cn n → ℝ),
      (∀ m, 0 < δ m) ∧ (∀ m, δ m ≤ 1) ∧ Tendsto δ atTop (nhds 0) ∧
      (∀ m, ContDiff ℝ (⊤ : ℕ∞) (φ m)) ∧ (∀ m x, 0 ≤ φ m x) ∧
      (∀ m, ∫ x, φ m x ∂(volume : Measure (Cn n)) = 1) ∧ (∀ m, HasCompactSupport (φ m)) ∧
      (∀ m x, δ m < ‖x‖ → φ m x = 0) := by
  let δ : ℕ → ℝ := fun m => min (1 / ((m : ℝ) + 1)) 1
  have hδpos : ∀ m, 0 < δ m := fun m => lt_min (by positivity) one_pos
  have hδle : ∀ m, δ m ≤ 1 := fun m => min_le_right _ _
  have hδtend : Tendsto δ atTop (nhds 0) := tendsto_min_one_div_add_one_one
  let b : ℕ → ContDiffBump (0 : Cn n) := fun m =>
    ⟨δ m / 2, δ m, half_pos (hδpos m), by linarith [hδpos m]⟩
  refine ⟨δ, fun m => (b m).normed (volume : Measure (Cn n)), hδpos, hδle, hδtend,
    fun m => (b m).contDiff_normed (n := ⊤), fun m x => (b m).nonneg_normed x,
    fun m => (b m).integral_normed, fun m => (b m).hasCompactSupport_normed, ?_⟩
  intro m x hx
  rw [← Function.notMem_support, (b m).support_normed_eq]
  simp only [Metric.mem_ball, dist_zero_right, not_lt]
  linarith [hδpos m]

theorem gnsLipschitz {n : ℕ} (hn : 0 < n) :
    ∃ C : ℝ, 0 < C ∧ ∀ (L : ℝ≥0) (W : Work.NN.Core.Cn n → ℂ), LipschitzWith L W → HasCompactSupport W →
      (MeasureTheory.eLpNorm W ((2 : ENNReal) * ((NNReal.conjExponent (2 * n) : NNReal) : ENNReal))) ^ 2 ≤
        ENNReal.ofReal C * MeasureTheory.eLpNorm W 2 MeasureTheory.volume *
          MeasureTheory.eLpNorm (fderiv ℝ W) 2 MeasureTheory.volume := by
  classical
  obtain ⟨C₀, hC₀pos, hGNS⟩ := gagliardoNirenbergGeomMean hn
  refine ⟨C₀, hC₀pos, ?_⟩
  intro L W hLip hcs
  set EX : ENNReal := (2 : ENNReal) * ((NNReal.conjExponent (2 * n) : NNReal) : ENNReal) with hEX
  -- exponent facts
  have hq1 : 1 ≤ (NNReal.conjExponent (2 * n)) := by
    rw [NNReal.conjExponent, one_le_div₀]
    · exact tsub_le_iff_right.mpr (le_add_right le_rfl)
    · refine tsub_pos_of_lt ?_
      have hn1 : (1 : NNReal) ≤ n := by exact_mod_cast hn
      nlinarith
  have hEXone : 1 ≤ EX := by
    rw [hEX]
    exact one_le_mul (by norm_num)
      (by exact_mod_cast hq1 : (1 : ENNReal) ≤ ((NNReal.conjExponent (2 * n) : NNReal) : ENNReal))
  have hEXtop : EX ≠ ⊤ := by
    rw [hEX]
    exact ENNReal.mul_ne_top (by norm_num) (by simp)
  -- the mollifier family
  obtain ⟨δ, φ, hδpos, hδle1, hδtend, hφcont, hφnonneg, hφint1, hφcs, hφsupp⟩ :=
    exists_mollifier_family_Cn n
  have hφint : ∀ m, Integrable (φ m) volume := fun m =>
    (hφcont m).continuous.integrable_of_hasCompactSupport (hφcs m)
  have hWcont : Continuous W := hLip.continuous
  obtain ⟨CW, hCW⟩ := hWcont.bounded_above_of_compact_support hcs
  have hCW' : ∀ x, ‖W x‖ ≤ max CW 0 := fun x => (hCW x).trans (le_max_left _ _)
  let Wm : ℕ → Cn n → ℂ := fun m =>
    MeasureTheory.convolution (φ m) W (ContinuousLinearMap.lsmul ℝ ℝ) volume
  have hWm_eq : ∀ m x, Wm m x = ∫ t, (φ m) t • W (x - t) ∂volume := by
    intro m x
    simp only [Wm]
    exact MeasureTheory.convolution_lsmul
  have hWm_fun : ∀ m, Wm m = fun y => ∫ t, (φ m) t • W (y - t) ∂volume :=
    fun m => funext (hWm_eq m)
  have hWm_cont : ∀ m, ContDiff ℝ 1 (Wm m) := by
    intro m
    have h := (hφcs m).contDiff_convolution_left (μ := volume) (ContinuousLinearMap.lsmul ℝ ℝ)
      (n := (1 : ℕ∞)) ((hφcont m).of_le (WithTop.coe_le_coe.mpr le_top))
      hWcont.locallyIntegrable
    simpa [Wm] using h
  have hWm_cs : ∀ m, HasCompactSupport (Wm m) := by
    intro m
    have h := (hφcs m).convolution (μ := volume) (ContinuousLinearMap.lsmul ℝ ℝ) hcs
    simpa [Wm] using h
  -- the derivative of the mollification
  have hfderiv : ∀ m x, fderiv ℝ (Wm m) x = ∫ t, (φ m) t • fderiv ℝ W (x - t) ∂volume := by
    intro m x
    rw [hWm_fun m]
    exact fderiv_convolution_of_lipschitz_tmp (n := n) hLip hcs (hφnonneg m) (hφint m) x
  have hL2 : ∀ m, eLpNorm (fderiv ℝ (Wm m)) 2 volume ≤ eLpNorm (fderiv ℝ W) 2 volume := by
    intro m
    have hg : AEMeasurable (fderiv ℝ W) volume := (measurable_fderiv ℝ W).aemeasurable
    have h := eLpNorm_integral_smul_sub_le (n := n) (ρ := φ m) (g := fderiv ℝ W)
      (hφnonneg m) (hφint m) (hφint1 m) hg
    calc eLpNorm (fderiv ℝ (Wm m)) 2 volume
        = eLpNorm (fun x => ∫ t, (φ m) t • fderiv ℝ W (x - t) ∂volume) 2 volume := by
          rw [funext (hfderiv m)]
      _ ≤ eLpNorm (fderiv ℝ W) 2 volume := h
  -- the smooth GNS applied to `Wm m`
  have hstep : ∀ m, (eLpNorm (Wm m) EX volume) ^ 2
      ≤ ENNReal.ofReal C₀ * eLpNorm (Wm m) 2 volume * eLpNorm (fderiv ℝ W) 2 volume := by
    intro m
    exact (hGNS (Wm m) (hWm_cont m) (hWm_cs m)).trans (by gcongr; exact hL2 m)
  -- finiteness
  have hWfinp : ∀ p : ℝ≥0∞, eLpNorm W p volume ≠ ⊤ := fun p =>
    ((hWcont.memLp_of_hasCompactSupport hcs).eLpNorm_lt_top).ne
  have hWmfinp : ∀ p : ℝ≥0∞, ∀ m, eLpNorm (Wm m) p volume ≠ ⊤ := fun p m =>
    (((hWm_cont m).continuous.memLp_of_hasCompactSupport (hWm_cs m)).eLpNorm_lt_top).ne
  have hDfin : eLpNorm (fderiv ℝ W) 2 volume ≠ ⊤ := by
    have hsupp : ∀ x ∉ tsupport W, fderiv ℝ W x = 0 := by
      intro x hx
      have hmem : (closure (Function.support W))ᶜ ∈ 𝓝 x :=
        isClosed_closure.isOpen_compl.mem_nhds hx
      have hev : W =ᶠ[𝓝 x] (0 : Cn n → ℂ) := by
        filter_upwards [hmem] with y hy
        simp only [Set.mem_compl_iff] at hy
        exact Function.notMem_support.mp fun h => hy (subset_closure h)
      rw [hev.fderiv_eq]
      simp
    have h := eLpNorm_le_of_support_subset_isCompact (p := (2 : ENNReal)) (f := fderiv ℝ W)
      (K := tsupport W) (C := ENNReal.ofReal (L : ℝ)) (by norm_num) (by norm_num) hcs.isCompact
      (measurable_fderiv ℝ W).aestronglyMeasurable
      (fun x _ => by
        rw [← ofReal_norm]
        exact ENNReal.ofReal_le_ofReal (norm_fderiv_le_of_lipschitz ℝ hLip))
      hsupp
    exact ne_of_lt (lt_of_le_of_lt h (ENNReal.mul_lt_top
      (lt_top_iff_ne_top.mpr ENNReal.ofReal_ne_top)
      (ENNReal.rpow_lt_top_of_nonneg (by norm_num) hcs.isCompact.measure_lt_top.ne)))
  -- real-valued version of the per-`m` bound
  have hstepR : ∀ m, (eLpNorm (Wm m) EX volume).toReal ^ 2
      ≤ C₀ * (eLpNorm (Wm m) 2 volume).toReal
        * (eLpNorm (fderiv ℝ W) 2 volume).toReal := by
    intro m
    have hne : ENNReal.ofReal C₀ * eLpNorm (Wm m) 2 volume * eLpNorm (fderiv ℝ W) 2 volume
        ≠ ⊤ :=
      ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hWmfinp 2 m)) hDfin
    have h := ENNReal.toReal_mono hne (hstep m)
    rwa [ENNReal.toReal_pow, ENNReal.toReal_mul, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal hC₀pos.le] at h
  -- support of the mollification
  have hsuppWm : ∀ m, Function.support (Wm m) ⊆ Metric.closedBall (0 : Cn n) 1 + tsupport W := by
    intro m
    have h1 : Function.support (Wm m) ⊆ Function.support (φ m) + Function.support W := by
      simp only [Wm]
      exact MeasureTheory.support_convolution_subset (μ := volume) (ContinuousLinearMap.lsmul ℝ ℝ)
    have h2 : Function.support (φ m) ⊆ Metric.closedBall (0 : Cn n) 1 := by
      intro t ht
      rw [Metric.mem_closedBall, dist_zero_right]
      by_contra h
      have h1 : δ m < ‖t‖ := lt_of_le_of_lt (hδle1 m) (not_le.mp h)
      exact ht (hφsupp m t h1)
    exact h1.trans (Set.add_subset_add h2 (subset_tsupport W))
  have hKsub : ∀ m, Function.support (fun x => Wm m x - W x)
      ⊆ Metric.closedBall (0 : Cn n) 1 + tsupport W := by
    intro m
    refine subset_trans (Function.support_sub (Wm m) W) (Set.union_subset (hsuppWm m) ?_)
    intro x hx
    exact ⟨0, by simp, x, subset_tsupport W hx, by simp⟩
  have hK : IsCompact (Metric.closedBall (0 : Cn n) 1 + tsupport W) :=
    (isCompact_closedBall 0 1).add hcs.isCompact
  have hmeas_sub : ∀ m, AEStronglyMeasurable (fun x => Wm m x - W x) volume := fun m =>
    ((hWm_cont m).continuous.sub hWcont).aestronglyMeasurable
  -- the uniform bound on the difference
  have hbdd : ∀ m x, ‖Wm m x - W x‖ ≤ (L : ℝ) * δ m := by
    intro m x
    have hint1 : Integrable (fun t : Cn n => (φ m) t • W (x - t)) volume := by
      have hcont : Continuous (fun t : Cn n => (φ m) t • W (x - t)) :=
        ((hφcont m).continuous).smul (hWcont.comp (continuous_const.sub continuous_id))
      refine Integrable.mono' ((hφint m).mul_const (max CW 0)) hcont.aestronglyMeasurable
        (Eventually.of_forall fun t => ?_)
      rw [norm_smul, Real.norm_of_nonneg (hφnonneg m t)]
      exact mul_le_mul_of_nonneg_left (hCW' (x - t)) (hφnonneg m t)
    have hdiff : Wm m x - W x = ∫ t, (φ m) t • (W (x - t) - W x) ∂volume := by
      have h1 : ∫ t, (φ m) t • W x ∂volume = W x := by
        rw [integral_smul_const, hφint1 m, one_smul]
      have h2 : ∫ t, (φ m) t • W (x - t) ∂volume - ∫ t, (φ m) t • W x ∂volume
          = ∫ t, (φ m) t • (W (x - t) - W x) ∂volume := by
        rw [← integral_sub hint1 ((hφint m).smul_const (W x))]
        congr 1 with t
        rw [smul_sub]
      rw [hWm_eq m x]
      conv_lhs => rw [← h1]
      exact h2
    have hpt : ∀ t : Cn n, (φ m) t * ‖W (x - t) - W x‖ ≤ (φ m) t * ((L : ℝ) * δ m) := by
      intro t
      by_cases h : ‖t‖ ≤ δ m
      · refine mul_le_mul_of_nonneg_left ?_ (hφnonneg m t)
        calc ‖W (x - t) - W x‖ ≤ (L : ℝ) * ‖x - t - x‖ := hLip.norm_sub_le (x - t) x
          _ = (L : ℝ) * ‖t‖ := by rw [sub_sub_cancel_left, norm_neg]
          _ ≤ (L : ℝ) * δ m := mul_le_mul_of_nonneg_left h L.coe_nonneg
      · rw [hφsupp m t (not_le.mp h), zero_mul, zero_mul]
    have hint2 : Integrable (fun t : Cn n => (φ m) t * ‖W (x - t) - W x‖) volume := by
      have hcont : Continuous (fun t : Cn n => (φ m) t * ‖W (x - t) - W x‖) :=
        ((hφcont m).continuous).mul
          (((hWcont.comp (continuous_const.sub continuous_id)).sub continuous_const)).norm
      refine Integrable.mono' ((hφint m).mul_const ((L : ℝ) * δ m)) hcont.aestronglyMeasurable
        (Eventually.of_forall fun t => ?_)
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hφnonneg m t) (norm_nonneg _))]
      exact hpt t
    calc ‖Wm m x - W x‖ = ‖∫ t, (φ m) t • (W (x - t) - W x) ∂volume‖ := by rw [hdiff]
      _ ≤ ∫ t, (φ m) t * ‖W (x - t) - W x‖ ∂volume := by
          refine (norm_integral_le_integral_norm _).trans_eq ?_
          refine integral_congr_ae (Eventually.of_forall fun t => ?_)
          simp only [norm_smul, Real.norm_of_nonneg (hφnonneg m t)]
      _ ≤ ∫ t, (φ m) t * ((L : ℝ) * δ m) ∂volume :=
          integral_mono hint2 ((hφint m).mul_const ((L : ℝ) * δ m)) hpt
      _ = (∫ t, (φ m) t ∂volume) * ((L : ℝ) * δ m) := by rw [integral_mul_const]
      _ = (L : ℝ) * δ m := by rw [hφint1 m, one_mul]
  have hc0 : ∀ m, 0 ≤ (L : ℝ) * δ m := fun m => mul_nonneg L.coe_nonneg (hδpos m).le
  have hc : Tendsto (fun m => (L : ℝ) * δ m) atTop (nhds 0) := by
    simpa using hδtend.const_mul (L : ℝ)
  obtain ⟨hlimEX, -⟩ := tendsto_toReal_eLpNorm_of_uniform (p := EX) hEXone hEXtop hK hKsub
    hmeas_sub (hWfinp EX) (fun m => hWmfinp EX m) hc0 hc hbdd
  obtain ⟨hlim2, -⟩ := tendsto_toReal_eLpNorm_of_uniform (p := 2) (by norm_num) (by norm_num) hK
    hKsub hmeas_sub (hWfinp 2) (fun m => hWmfinp 2 m) hc0 hc hbdd
  -- pass to the limit
  have hltu : Tendsto (fun m => (eLpNorm (Wm m) EX volume).toReal ^ 2) atTop
      (nhds ((eLpNorm W EX volume).toReal ^ 2)) := hlimEX.pow 2
  have hrt : Tendsto (fun m => C₀ * (eLpNorm (Wm m) 2 volume).toReal
      * (eLpNorm (fderiv ℝ W) 2 volume).toReal) atTop
      (nhds (C₀ * (eLpNorm W 2 volume).toReal
        * (eLpNorm (fderiv ℝ W) 2 volume).toReal)) := by
    have h2 : Tendsto (fun m => C₀ * (eLpNorm (Wm m) 2 volume).toReal) atTop
        (nhds (C₀ * (eLpNorm W 2 volume).toReal)) :=
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => C₀) atTop (nhds C₀)).mul hlim2
    exact h2.mul_const ((eLpNorm (fderiv ℝ W) 2 volume).toReal)
  have hreal : (eLpNorm W EX volume).toReal ^ 2
      ≤ C₀ * (eLpNorm W 2 volume).toReal * (eLpNorm (fderiv ℝ W) 2 volume).toReal :=
    le_of_tendsto_of_tendsto hltu hrt (Eventually.of_forall hstepR)
  -- back to `ℝ≥0∞`
  calc (eLpNorm W EX volume) ^ 2
      = ENNReal.ofReal ((eLpNorm W EX volume).toReal ^ 2) := by
        conv_lhs => rw [← ENNReal.ofReal_toReal (hWfinp EX)]
        rw [pow_two, ← ENNReal.ofReal_mul ENNReal.toReal_nonneg]
        simp only [pow_two]
    _ ≤ ENNReal.ofReal (C₀ * (eLpNorm W 2 volume).toReal
          * (eLpNorm (fderiv ℝ W) 2 volume).toReal) := ENNReal.ofReal_le_ofReal hreal
    _ = ENNReal.ofReal C₀ * eLpNorm W 2 volume * eLpNorm (fderiv ℝ W) 2 volume := by
        conv_rhs => rw [← ENNReal.ofReal_toReal (hWfinp 2), ← ENNReal.ofReal_toReal hDfin,
          ← ENNReal.ofReal_mul hC₀pos.le, ← ENNReal.ofReal_mul (by positivity)]

end Work.NN.Core
