import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
import Mathlib.Order.CompletePartialOrder

namespace Commons.Analysis.Sobolev

open MeasureTheory Filter
open scoped Topology Convolution ContDiff Pointwise

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

theorem exists_mollifier_sequence :
    ∃ (ρ : ℕ → E → ℝ) (R : ℕ → ℝ),
      (∀ n, ContDiff ℝ (⊤ : ℕ∞) (ρ n)) ∧ (∀ n, HasCompactSupport (ρ n)) ∧
      (∀ n, Continuous (ρ n)) ∧ (∀ n, Integrable (ρ n) (volume : Measure E)) ∧
      (∀ n x, 0 ≤ ρ n x) ∧ (∀ n, ∫ x, ρ n x = 1) ∧
      (∀ n, 0 ≤ R n) ∧ Tendsto R atTop (𝓝 0) ∧
      (∀ n x, R n < ‖x‖ → ρ n x = 0) := by
  let f : ℕ → ContDiffBump (0 : E) :=
    fun n => ⟨1 / ((n:ℝ) + 1), 2 / ((n:ℝ) + 1), by positivity,
      by rw [div_lt_div_iff_of_pos_right (by positivity : (0:ℝ) < (n:ℝ)+1)]; norm_num⟩
  refine ⟨fun n => (f n).normed volume, fun n => 2 / ((n:ℝ) + 1),
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro n; exact (f n).contDiff_normed
  · intro n; exact (f n).hasCompactSupport_normed
  · intro n; exact (f n).continuous_normed
  · intro n; exact (f n).integrable_normed
  · intro n x; exact (f n).nonneg_normed x
  · intro n; exact (f n).integral_normed
  · intro n; positivity
  · convert (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul 2 using 1
    · ext n; rw [div_eq_mul_one_div]
    · rw [mul_zero]
  · intro n x hx
    have hmem : x ∉ Function.support ((f n).normed volume) := by
      rw [(f n).support_normed_eq]
      simp only [Metric.mem_ball, dist_zero_right, not_lt]
      exact le_of_lt hx
    exact Function.notMem_support.mp hmem

theorem tendsto_uniform_mollification
    (ρ : ℕ → E → ℝ) (R : ℕ → ℝ)
    (hρnn : ∀ n x, 0 ≤ ρ n x) (hρi : ∀ n, Integrable (ρ n) (volume : Measure E))
    (hρ1 : ∀ n, ∫ x, ρ n x = 1)
    (hR : Tendsto R atTop (𝓝 0))
    (hRs : ∀ n x, R n < ‖x‖ → ρ n x = 0) (hρc : ∀ n, Continuous (ρ n))
    {g : E → ℝ} (hg : UniformContinuous g) :
    ∀ ε > 0, ∀ᶠ n in atTop, ∀ x, |(∫ t, ρ n t * g (x - t)) - g x| ≤ ε := by
  intro ε hε
  obtain ⟨δ, hδpos, hδ⟩ := Metric.uniformContinuous_iff.mp hg ε hε
  have hRev : ∀ᶠ n in atTop, R n < δ := hR.eventually_lt_const hδpos
  have hgc : Continuous g := hg.continuous
  filter_upwards [hRev] with n hn x
  have hρcs : HasCompactSupport (ρ n) := by
    refine IsCompact.of_isClosed_subset (isCompact_closedBall (0:E) (R n))
      (isClosed_tsupport (ρ n)) (closure_minimal ?_ Metric.isClosed_closedBall)
    intro y hy
    rw [Function.mem_support] at hy
    rw [Metric.mem_closedBall, dist_zero_right]
    by_contra h
    rw [not_le] at h
    exact hy (hRs n y h)
  have hInt1 : Integrable (fun t => ρ n t * g (x - t)) :=
    ((hρc n).mul (hgc.comp (continuous_const.sub continuous_id))).integrable_of_hasCompactSupport
      (hρcs.mul_right (f' := fun t => g (x - t)))
  have hInt2 : Integrable (fun t => ρ n t * g x) := (hρi n).mul_const (g x)
  have key : (∫ t, ρ n t * g (x - t)) - g x = ∫ t, ρ n t * (g (x - t) - g x) := by
    have h1 : ∫ t, ρ n t * g x = g x := by rw [integral_mul_const, hρ1 n, one_mul]
    calc (∫ t, ρ n t * g (x - t)) - g x
        = (∫ t, ρ n t * g (x - t)) - ∫ t, ρ n t * g x := by rw [h1]
      _ = ∫ t, (ρ n t * g (x - t) - ρ n t * g x) := by rw [integral_sub hInt1 hInt2]
      _ = ∫ t, ρ n t * (g (x - t) - g x) := by
            apply integral_congr_ae; filter_upwards with t; ring
  rw [key]
  calc |∫ t, ρ n t * (g (x - t) - g x)|
      ≤ ∫ t, |ρ n t * (g (x - t) - g x)| := by
        simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm
          (fun t => ρ n t * (g (x - t) - g x))
    _ = ∫ t, ρ n t * |g (x - t) - g x| := by
        apply integral_congr_ae; filter_upwards with t
        rw [abs_mul, abs_of_nonneg (hρnn n t)]
    _ ≤ ∫ t, ρ n t * ε := by
        apply integral_mono_of_nonneg
        · filter_upwards with t; exact mul_nonneg (hρnn n t) (abs_nonneg _)
        · exact (hρi n).mul_const ε
        · filter_upwards with t
          by_cases ht : ρ n t = 0
          · rw [ht, zero_mul, zero_mul]
          · have hle : ‖t‖ ≤ R n := by
              by_contra h
              rw [not_le] at h
              exact ht (hRs n t h)
            have hdt : dist (x - t) x < δ := by
              rw [dist_eq_norm, show x - t - x = -t from by abel, norm_neg]
              linarith
            have hb := hδ hdt
            rw [Real.dist_eq] at hb
            exact mul_le_mul_of_nonneg_left (le_of_lt hb) (hρnn n t)
    _ = ε := by
        rw [integral_mul_const, hρ1 n, one_mul]

private def moll (ρ₀ g : E → ℝ) : E → ℝ :=
  ρ₀ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g

end

theorem integral_mul_eq_neg_integral_fderiv_of_contDiff_two {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] (w ψ : E → ℝ) (v : E) (hw : MeasureTheory.MemLp w 2 (MeasureTheory.volume : MeasureTheory.Measure E)) (hψ : MeasureTheory.MemLp ψ 2 (MeasureTheory.volume : MeasureTheory.Measure E)) (hS : ∀ χ : SchwartzMap E ℝ, ∫ x, (χ : E → ℝ) x * w x = -∫ x, (fderiv ℝ (χ : E → ℝ) x) v * ψ x) (φ : E → ℝ) (hφ : ContDiff ℝ 2 φ) (hφc : HasCompactSupport φ) : ∫ x, φ x * w x = -∫ x, (fderiv ℝ φ x) v * ψ x := by
  classical
  obtain ⟨ρ, R, hρsmooth, hρcs, hρcont, hρint, hρnn, hρ1, hRpos, hRtend, hRs⟩ :=
    exists_mollifier_sequence (E := E)
  have hφC1 : ContDiff ℝ 1 φ := hφ.of_le (by norm_num)
  have hφuc : UniformContinuous φ := hφc.uniformContinuous_of_continuous hφ.continuous
  have hφli : LocallyIntegrable φ (volume : Measure E) := hφ.continuous.locallyIntegrable
  have hχsmooth : ∀ n, ContDiff ℝ (⊤ : ℕ∞) (moll (ρ n) φ) := by
    intro n
    exact (hρcs n).contDiff_convolution_left (ContinuousLinearMap.lsmul ℝ ℝ) (hρsmooth n) hφli
  have hχcs : ∀ n, HasCompactSupport (moll (ρ n) φ) := by
    intro n
    exact (hρcs n).convolution (ContinuousLinearMap.lsmul ℝ ℝ) hφc
  have hχval : ∀ n x, moll (ρ n) φ x = ∫ t, ρ n t * φ (x - t) := by
    intro n x
    simp only [moll, MeasureTheory.convolution_def, ContinuousLinearMap.lsmul_apply, smul_eq_mul]
  have hderiv : ∀ n x, (fderiv ℝ (moll (ρ n) φ) x) v
      = ∫ t, ρ n t * ((fderiv ℝ φ (x - t)) v) := by
    intro n x
    have hfd := (hφc.hasFDerivAt_convolution_right (ContinuousLinearMap.lsmul ℝ ℝ)
      (hρint n).locallyIntegrable hφC1 x).fderiv
    simp only [moll]
    rw [hfd]
    rw [MeasureTheory.convolution_precompR_apply (L := ContinuousLinearMap.lsmul ℝ ℝ) (μ := volume)
      (f := ρ n) (g := fderiv ℝ φ) (hρint n).locallyIntegrable (hφc.fderiv ℝ)
      (hφ.continuous_fderiv (by norm_num)) x v]
    rw [MeasureTheory.convolution_def]
    simp only [ContinuousLinearMap.lsmul_apply, smul_eq_mul]
  have hconv_phi : ∀ ε > 0, ∀ᶠ n in atTop, ∀ x, |moll (ρ n) φ x - φ x| ≤ ε := by
    intro ε hε
    filter_upwards [tendsto_uniform_mollification ρ R hρnn hρint hρ1 hRtend hRs hρcont
      (g := φ) hφuc ε hε] with n hn x
    rw [hχval n x]; exact hn x
  have hgcont : Continuous (fun x => (fderiv ℝ φ x) v) :=
    (hφ.continuous_fderiv (by norm_num)).clm_apply continuous_const
  have hgcs : HasCompactSupport (fun x => (fderiv ℝ φ x) v) :=
    (hφc.fderiv ℝ).comp_left (g := fun L : E →L[ℝ] ℝ => L v) (by simp)
  have hguc : UniformContinuous (fun x => (fderiv ℝ φ x) v) :=
    hgcs.uniformContinuous_of_continuous hgcont
  obtain ⟨Cg, hCg⟩ := hgcont.bounded_above_of_compact_support hgcs
  have hconv_deriv : ∀ ε > 0, ∀ᶠ n in atTop, ∀ x,
      |(fderiv ℝ (moll (ρ n) φ) x) v - (fderiv ℝ φ x) v| ≤ ε := by
    intro ε hε
    filter_upwards [tendsto_uniform_mollification ρ R hρnn hρint hρ1 hRtend hRs hρcont
      (g := fun x => (fderiv ℝ φ x) v) hguc ε hε] with n hn x
    rw [hderiv n x]; exact hn x
  obtain ⟨Cφ, hCφ⟩ := hφ.continuous.bounded_above_of_compact_support hφc
  let K : Set E := tsupport φ + Metric.closedBall (0 : E) 1
  have hK : IsCompact K := hφc.isCompact.add (isCompact_closedBall 0 1)
  have hKmeas : MeasurableSet K := hK.isClosed.measurableSet
  have hR1 : ∀ᶠ n in atTop, R n < 1 := hRtend.eventually_lt_const one_pos
  have hKmem : ∀ x, x ∉ K → x ∉ tsupport φ := by
    intro x hx hmem
    refine hx ?_
    have h0 : (0 : E) ∈ Metric.closedBall (0 : E) 1 := by
      rw [Metric.mem_closedBall, dist_self]; norm_num
    simpa using (Set.add_mem_add hmem h0 :
      x + 0 ∈ tsupport φ + Metric.closedBall (0 : E) 1)
  have hχsupp : ∀ᶠ n in atTop, ∀ x, x ∉ K → moll (ρ n) φ x = 0 := by
    filter_upwards [hR1] with n hn x hx
    rw [hχval n x]
    apply integral_eq_zero_of_ae
    filter_upwards with t
    by_cases ht : ρ n t = 0
    · simp only [ht, zero_mul, Pi.zero_apply]
    · have hle : ‖t‖ ≤ R n := by
        by_contra h; rw [not_le] at h; exact ht (hRs n t h)
      have hxnt : x - t ∉ tsupport φ := by
        intro hmem
        refine hx ?_
        have h0 : t ∈ Metric.closedBall (0 : E) 1 := by
          rw [Metric.mem_closedBall, dist_zero_right]; linarith [hle, hn]
        simpa only [sub_add_cancel] using (Set.add_mem_add hmem h0 :
          (x - t) + t ∈ tsupport φ + Metric.closedBall (0 : E) 1)
      rw [image_eq_zero_of_notMem_tsupport hxnt, mul_zero, Pi.zero_apply]
  have hχdsupp : ∀ᶠ n in atTop, ∀ x, x ∉ K → (fderiv ℝ (moll (ρ n) φ) x) v = 0 := by
    filter_upwards [hR1] with n hn x hx
    rw [hderiv n x]
    apply integral_eq_zero_of_ae
    filter_upwards with t
    by_cases ht : ρ n t = 0
    · simp only [ht, zero_mul, Pi.zero_apply]
    · have hle : ‖t‖ ≤ R n := by
        by_contra h; rw [not_le] at h; exact ht (hRs n t h)
      have hxnt : x - t ∉ tsupport φ := by
        intro hmem
        refine hx ?_
        have h0 : t ∈ Metric.closedBall (0 : E) 1 := by
          rw [Metric.mem_closedBall, dist_zero_right]; linarith [hle, hn]
        simpa only [sub_add_cancel] using (Set.add_mem_add hmem h0 :
          (x - t) + t ∈ tsupport φ + Metric.closedBall (0 : E) 1)
      have hfd : fderiv ℝ φ (x - t) = 0 :=
        Function.notMem_support.mp (fun h => hxnt (support_fderiv_subset ℝ h))
      rw [hfd, zero_apply, mul_zero, Pi.zero_apply]
  have hgsupp : ∀ x, x ∉ K → (fderiv ℝ φ x) v = 0 := by
    intro x hx
    have hfd : fderiv ℝ φ x = 0 :=
      Function.notMem_support.mp (fun h => hKmem x hx (support_fderiv_subset ℝ h))
    rw [hfd, zero_apply]
  have hwloc : LocallyIntegrable w (volume : Measure E) := hw.locallyIntegrable (by norm_num)
  have hwK : Integrable (fun x => (Cφ + 1) * |w x|) (volume.restrict K) := by
    have h1 : Integrable w (volume.restrict K) := hwloc.integrableOn_isCompact hK
    have h2 : Integrable (fun a => |w a|) (volume.restrict K) :=
      Integrable.congr h1.norm (Filter.Eventually.of_forall (fun a => Real.norm_eq_abs (w a)))
    exact h2.const_mul (Cφ + 1)
  have hbdφint : Integrable (K.indicator (fun x => (Cφ + 1) * |w x|)) volume :=
    (integrable_indicator_iff hKmeas).mpr hwK
  have hψloc : LocallyIntegrable ψ (volume : Measure E) := hψ.locallyIntegrable (by norm_num)
  have hψK : Integrable (fun x => (Cg + 1) * |ψ x|) (volume.restrict K) := by
    have h1 : Integrable ψ (volume.restrict K) := hψloc.integrableOn_isCompact hK
    have h2 : Integrable (fun a => |ψ a|) (volume.restrict K) :=
      Integrable.congr h1.norm (Filter.Eventually.of_forall (fun a => Real.norm_eq_abs (ψ a)))
    exact h2.const_mul (Cg + 1)
  have hbdgint : Integrable (K.indicator (fun x => (Cg + 1) * |ψ x|)) volume :=
    (integrable_indicator_iff hKmeas).mpr hψK
  have hptχ : ∀ x, Tendsto (fun n => moll (ρ n) φ x) atTop (𝓝 (φ x)) := by
    intro x
    rw [Metric.tendsto_nhds]
    intro ε hε
    filter_upwards [hconv_phi (ε/2) (by positivity)] with n hn
    rw [Real.dist_eq]
    linarith [hn x]
  have hptg : ∀ x, Tendsto (fun n => (fderiv ℝ (moll (ρ n) φ) x) v) atTop
      (𝓝 ((fderiv ℝ φ x) v)) := by
    intro x
    rw [Metric.tendsto_nhds]
    intro ε hε
    filter_upwards [hconv_deriv (ε/2) (by positivity)] with n hn
    rw [Real.dist_eq]
    linarith [hn x]
  have htend_phi : Tendsto (fun n => ∫ x, moll (ρ n) φ x * w x) atTop
      (𝓝 (∫ x, φ x * w x)) := by
    refine tendsto_integral_filter_of_dominated_convergence (μ := volume)
      (F := fun n => fun x => moll (ρ n) φ x * w x) (f := fun x => φ x * w x)
      (K.indicator (fun x => (Cφ + 1) * |w x|)) ?_ ?_ hbdφint ?_
    · filter_upwards with n
      exact ((hχsmooth n).continuous.aestronglyMeasurable).mul hw.aestronglyMeasurable
    · filter_upwards [hconv_phi 1 one_pos, hχsupp] with n hn1 hnsupp
      filter_upwards with x
      have key := hn1 x
      have hbound : ‖moll (ρ n) φ x‖ ≤ Cφ + 1 := by
        have hφb : |φ x| ≤ Cφ := by simpa only [Real.norm_eq_abs] using hCφ x
        rw [Real.norm_eq_abs]
        calc |moll (ρ n) φ x| = |(moll (ρ n) φ x - φ x) + φ x| := by ring_nf
          _ ≤ |moll (ρ n) φ x - φ x| + |φ x| := abs_add_le _ _
          _ ≤ Cφ + 1 := by linarith
      by_cases hx : x ∈ K
      · rw [Set.indicator_of_mem hx]
        calc ‖moll (ρ n) φ x * w x‖ = ‖moll (ρ n) φ x‖ * ‖w x‖ := norm_mul _ _
          _ ≤ (Cφ + 1) * ‖w x‖ := mul_le_mul_of_nonneg_right hbound (norm_nonneg _)
          _ = (Cφ + 1) * |w x| := by rw [Real.norm_eq_abs]
      · rw [Set.indicator_of_notMem hx, hnsupp x hx, zero_mul, norm_zero]
    · exact Filter.Eventually.of_forall (fun x => (hptχ x).mul_const (w x))
  have htend_deriv : Tendsto (fun n => ∫ x, (fderiv ℝ (moll (ρ n) φ) x) v * ψ x) atTop
      (𝓝 (∫ x, (fderiv ℝ φ x) v * ψ x)) := by
    refine tendsto_integral_filter_of_dominated_convergence (μ := volume)
      (F := fun n => fun x => (fderiv ℝ (moll (ρ n) φ) x) v * ψ x)
      (f := fun x => (fderiv ℝ φ x) v * ψ x)
      (K.indicator (fun x => (Cg + 1) * |ψ x|)) ?_ ?_ hbdgint ?_
    · filter_upwards with n
      exact (((hχsmooth n).continuous_fderiv (by simp)).clm_apply continuous_const
        ).aestronglyMeasurable.mul hψ.aestronglyMeasurable
    · filter_upwards [hconv_deriv 1 one_pos, hχdsupp] with n hn1 hnsupp
      filter_upwards with x
      have key := hn1 x
      have hbound : ‖(fderiv ℝ (moll (ρ n) φ) x) v‖ ≤ Cg + 1 := by
        have hgb : |(fderiv ℝ φ x) v| ≤ Cg := by simpa only [Real.norm_eq_abs] using hCg x
        rw [Real.norm_eq_abs]
        calc |(fderiv ℝ (moll (ρ n) φ) x) v|
            = |((fderiv ℝ (moll (ρ n) φ) x) v - (fderiv ℝ φ x) v) + (fderiv ℝ φ x) v| := by
              ring_nf
          _ ≤ |(fderiv ℝ (moll (ρ n) φ) x) v - (fderiv ℝ φ x) v| + |(fderiv ℝ φ x) v| :=
              abs_add_le _ _
          _ ≤ Cg + 1 := by linarith
      by_cases hx : x ∈ K
      · rw [Set.indicator_of_mem hx]
        calc ‖(fderiv ℝ (moll (ρ n) φ) x) v * ψ x‖
            = ‖(fderiv ℝ (moll (ρ n) φ) x) v‖ * ‖ψ x‖ := norm_mul _ _
          _ ≤ (Cg + 1) * ‖ψ x‖ := mul_le_mul_of_nonneg_right hbound (norm_nonneg _)
          _ = (Cg + 1) * |ψ x| := by rw [Real.norm_eq_abs]
      · rw [Set.indicator_of_notMem hx, hnsupp x hx, zero_mul, norm_zero]
    · exact Filter.Eventually.of_forall (fun x => (hptg x).mul_const (ψ x))
  have hSχ : ∀ n, ∫ x, moll (ρ n) φ x * w x
      = -∫ x, (fderiv ℝ (moll (ρ n) φ) x) v * ψ x := by
    intro n
    exact hS ((hχcs n).toSchwartzMap (hχsmooth n))
  have h2 : Tendsto (fun n => ∫ x, moll (ρ n) φ x * w x) atTop
      (𝓝 (-∫ x, (fderiv ℝ φ x) v * ψ x)) := by
    have heq : (fun n => ∫ x, moll (ρ n) φ x * w x)
        = fun n => -∫ x, (fderiv ℝ (moll (ρ n) φ) x) v * ψ x := by
      funext n; exact hSχ n
    rw [heq]
    exact htend_deriv.neg
  exact tendsto_nhds_unique htend_phi h2



end Commons.Analysis.Sobolev