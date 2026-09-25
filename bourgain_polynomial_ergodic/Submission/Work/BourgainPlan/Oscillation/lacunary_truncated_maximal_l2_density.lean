import Mathlib
import Submission.Work.BourgainPlan.Oscillation.commons_deps
import Submission.Work.BourgainPlan.Oscillation.trigP_dense
import Submission.Commons.Analysis.ExponentialSums.quadratic_kernel_model_maximal_l2

open MeasureTheory Finset Filter
open scoped ENNReal Topology

namespace Work.BourgainPlan.Oscillation

noncomputable section

/-! ## Auxiliary facts

The `L²(mu01)`-extension of the lacunary truncated maximal estimate.  The proof follows the
classical pattern: prove the estimate on the dense family of trigonometric polynomials
(hypothesis `hbound`), then pass to the limit in `L²` with Fatou's lemma, using the
`L²`-convergence of the trigonometric approximations to supply the pointwise convergence of the
individual projections. -/

lemma isProbabilityMeasure_mu01 : IsProbabilityMeasure Lacunary.mu01 :=
  ⟨by rw [Lacunary.mu01, Measure.restrict_apply_univ, Real.volume_Ioc]; norm_num⟩

lemma memLp_trigP (s : Finset ℤ) (f : ℤ → ℂ) :
    MemLp (Lacunary.trigP s f) 2 Lacunary.mu01 := by
  haveI := Lacunary.isFiniteMeasure_mu01
  exact MemLp.of_bound (Lacunary.measurable_trigP s f).aestronglyMeasurable _
    (Filter.Eventually.of_forall (fun θ => Lacunary.norm_trigP_le s f θ))

/-- The truncated lacunary projection integral, against the reference measure `mu01`. -/
noncomputable def TLac (ρ : ℝ) (i : ℕ) (x : ℤ) (g : ℝ → ℂ) : ℂ :=
  ∫ θ, (if |θ| ≤ Lacunary.cc ρ i then (1 : ℂ) else 0) * g θ * Lacunary.Echar x θ ∂Lacunary.mu01

lemma wLac_measurable (ρ : ℝ) (i : ℕ) :
    Measurable (fun θ : ℝ => if |θ| ≤ Lacunary.cc ρ i then (1 : ℂ) else 0) :=
  Measurable.ite (measurableSet_le continuous_abs.measurable measurable_const)
    measurable_const measurable_const

lemma wLac_norm_le (ρ : ℝ) (i : ℕ) (θ : ℝ) :
    ‖(if |θ| ≤ Lacunary.cc ρ i then (1 : ℂ) else 0)‖ ≤ 1 := by split <;> simp

/-- The integrand of `TLac` is integrable when `g ∈ L²`. -/
lemma integrable_wmul (ρ : ℝ) (i : ℕ) (x : ℤ) {g : ℝ → ℂ} (hg : MemLp g 2 Lacunary.mu01) :
    Integrable (fun θ => (if |θ| ≤ Lacunary.cc ρ i then (1 : ℂ) else 0) * g θ
      * Lacunary.Echar x θ) Lacunary.mu01 := by
  haveI := Lacunary.isFiniteMeasure_mu01
  have hg1 : Integrable (fun θ => ‖g θ‖) Lacunary.mu01 :=
    (hg.integrable (by norm_num)).norm
  refine Integrable.mono' hg1 ?_ ?_
  · exact (((wLac_measurable ρ i).aestronglyMeasurable.mul hg.aestronglyMeasurable).mul
      (Lacunary.continuous_Echar x).measurable.aestronglyMeasurable)
  · filter_upwards with θ
    rw [norm_mul, norm_mul, Lacunary.norm_Echar, mul_one]
    exact mul_le_of_le_one_left (norm_nonneg (g θ)) (wLac_norm_le ρ i θ)

/-- The `L²`-norm of a difference of `Lp` classes is the `L²`-seminorm of the difference of the
representatives. -/
lemma norm_toLp_sub_toLp {g h : ℝ → ℂ} (hg : MemLp g 2 Lacunary.mu01)
    (hh : MemLp h 2 Lacunary.mu01) :
    ‖hg.toLp - hh.toLp‖ = (eLpNorm (fun θ => g θ - h θ) 2 Lacunary.mu01).toReal := by
  rw [Lp.norm_def]
  congr 1
  refine eLpNorm_congr_ae ?_
  filter_upwards [Lp.coeFn_sub hg.toLp hh.toLp, MemLp.coeFn_toLp hg, MemLp.coeFn_toLp hh]
    with θ h1 h2 h3
  rw [h1, Pi.sub_apply, h2, h3]

/-- Cauchy--Schwarz for the truncated projection: the difference of two projections is bounded by
the `L²`-distance of the inputs. -/
lemma norm_TLac_sub_le (ρ : ℝ) (i : ℕ) (x : ℤ) {g h : ℝ → ℂ}
    (hg : MemLp g 2 Lacunary.mu01) (hh : MemLp h 2 Lacunary.mu01) :
    ‖TLac ρ i x g - TLac ρ i x h‖ ≤ ‖hg.toLp - hh.toLp‖ := by
  haveI hfin := Lacunary.isFiniteMeasure_mu01
  haveI hprob := isProbabilityMeasure_mu01
  have hsub : TLac ρ i x g - TLac ρ i x h
      = ∫ θ, (if |θ| ≤ Lacunary.cc ρ i then (1 : ℂ) else 0) * (g θ - h θ)
          * Lacunary.Echar x θ ∂Lacunary.mu01 := by
    rw [TLac, TLac, ← integral_sub (integrable_wmul ρ i x hg) (integrable_wmul ρ i x hh)]
    exact integral_congr_ae (Filter.Eventually.of_forall (fun θ => by ring))
  rw [hsub]
  have hmain : ‖∫ θ, (if |θ| ≤ Lacunary.cc ρ i then (1 : ℂ) else 0) * (g θ - h θ)
        * Lacunary.Echar x θ ∂Lacunary.mu01‖ ≤ ‖hg.toLp - hh.toLp‖ := by
    have hgm : MemLp (fun θ => g θ - h θ) 2 Lacunary.mu01 := hg.sub hh
    have h1 : ‖∫ θ, (if |θ| ≤ Lacunary.cc ρ i then (1 : ℂ) else 0) * (g θ - h θ)
          * Lacunary.Echar x θ ∂Lacunary.mu01‖
        ≤ ∫ θ, ‖(if |θ| ≤ Lacunary.cc ρ i then (1 : ℂ) else 0) * (g θ - h θ)
          * Lacunary.Echar x θ‖ ∂Lacunary.mu01 := norm_integral_le_integral_norm _
    have h2 : ∫ θ, ‖(if |θ| ≤ Lacunary.cc ρ i then (1 : ℂ) else 0) * (g θ - h θ)
          * Lacunary.Echar x θ‖ ∂Lacunary.mu01 ≤ ∫ θ, ‖g θ - h θ‖ ∂Lacunary.mu01 := by
      refine integral_mono (integrable_wmul ρ i x hgm).norm (hgm.integrable (by norm_num)).norm ?_
      intro θ
      simp only []
      rw [norm_mul, norm_mul, Lacunary.norm_Echar, mul_one]
      exact mul_le_of_le_one_left (norm_nonneg (g θ - h θ)) (wLac_norm_le ρ i θ)
    have h3 : ∫ θ, ‖g θ - h θ‖ ∂Lacunary.mu01
        = (eLpNorm (fun θ => g θ - h θ) 1 Lacunary.mu01).toReal := by
      rw [eLpNorm_one_eq_lintegral_enorm hgm.aestronglyMeasurable,
        ← ofReal_integral_norm_eq_lintegral_enorm (f := fun θ => g θ - h θ)
          (hgm.integrable (by norm_num)),
        ENNReal.toReal_ofReal (integral_nonneg (fun θ => norm_nonneg _))]
    have h4 : (eLpNorm (fun θ => g θ - h θ) 1 Lacunary.mu01).toReal
        ≤ (eLpNorm (fun θ => g θ - h θ) 2 Lacunary.mu01).toReal :=
      ENNReal.toReal_mono hgm.eLpNorm_lt_top.ne
        (eLpNorm_le_eLpNorm_of_exponent_le (by norm_num))
    have h5 : (eLpNorm (fun θ => g θ - h θ) 2 Lacunary.mu01).toReal
        = ‖hg.toLp - hh.toLp‖ := (norm_toLp_sub_toLp hg hh).symm
    calc ‖∫ θ, (if |θ| ≤ Lacunary.cc ρ i then (1 : ℂ) else 0) * (g θ - h θ)
          * Lacunary.Echar x θ ∂Lacunary.mu01‖
        ≤ ∫ θ, ‖g θ - h θ‖ ∂Lacunary.mu01 := le_trans h1 h2
      _ = (eLpNorm (fun θ => g θ - h θ) 1 Lacunary.mu01).toReal := h3
      _ ≤ (eLpNorm (fun θ => g θ - h θ) 2 Lacunary.mu01).toReal := h4
      _ = ‖hg.toLp - hh.toLp‖ := h5
  exact hmain

/-- `(liminf u)^2 ≤ liminf (u^2)` in `ℝ≥0∞`. -/
lemma liminf_sq_le_liminf_sq {ι : Type*} {l : Filter ι} {u : ι → ℝ≥0∞} :
    (Filter.liminf u l) ^ 2 ≤ Filter.liminf (fun a => (u a) ^ 2) l := by
  simp only [pow_two]
  simp_rw [Filter.liminf_eq_iSup_iInf]
  simp_rw [iSup_subtype']
  simp_rw [ENNReal.mul_iSup, ENNReal.iSup_mul]
  refine iSup_le fun s => ?_
  refine iSup_le fun t => ?_
  refine le_trans (le_iInf₂ fun a ha => mul_le_mul' (iInf₂_le a ha.2) (iInf₂_le a ha.1))
    (le_iSup (fun w : {w : Set ι // w ∈ l} => ⨅ a ∈ w.1, u a * u a)
      ⟨s.1 ∩ t.1, l.inter_mem s.2 t.2⟩)

lemma liminf_rpow_two_le {ι : Type*} {l : Filter ι} {u : ι → ℝ≥0∞} :
    (Filter.liminf u l) ^ (2 : ℝ) ≤ Filter.liminf (fun a => (u a) ^ (2 : ℝ)) l := by
  have h := liminf_sq_le_liminf_sq (l := l) (u := u)
  simp_rw [ENNReal.rpow_two]
  exact h

theorem lacunary_truncated_maximal_l2_density (ρ : ℝ) (hρ : 1 < ρ) (C : ℝ) (hC : 0 < C)
    (hbound : ∀ (f : ℤ → ℂ) (s : Finset ℤ), (∀ n, n ∉ s → f n = 0) →
      (∫⁻ x : ℤ, (⨆ i : ℕ, ‖∫ θ in (0:ℝ)..1,
          (if |θ| ≤ Lacunary.cc ρ i then (1:ℂ) else 0) * Lacunary.trigP s f θ
            * Lacunary.Echar x θ‖ₑ) ^ (2 : ℝ) ∂MeasureTheory.Measure.count)
        ≤ ENNReal.ofReal (C ^ 2) * ∫⁻ x : ℤ, ‖f x‖ₑ ^ (2 : ℝ) ∂MeasureTheory.Measure.count) :
    ∀ (h : ℝ → ℂ), MemLp h 2 Lacunary.mu01 →
      (∫⁻ x : ℤ, (⨆ i : ℕ, ‖∫ θ in (0:ℝ)..1,
          (if |θ| ≤ Lacunary.cc ρ i then (1:ℂ) else 0) * h θ
            * Lacunary.Echar x θ‖ₑ) ^ (2 : ℝ) ∂MeasureTheory.Measure.count)
        ≤ ENNReal.ofReal (C ^ 2) * ∫⁻ θ : ℝ, ‖h θ‖ₑ ^ (2 : ℝ) ∂Lacunary.mu01 := by
  intro h hh
  haveI hfin : IsFiniteMeasure Lacunary.mu01 := Lacunary.isFiniteMeasure_mu01
  haveI hprob : IsProbabilityMeasure Lacunary.mu01 := isProbabilityMeasure_mu01
  -- the hypothesis, in the `mu01`-form
  have hbound' : ∀ (f : ℤ → ℂ) (s : Finset ℤ), (∀ n, n ∉ s → f n = 0) →
      (∫⁻ x : ℤ, (⨆ i : ℕ, ‖TLac ρ i x (Lacunary.trigP s f)‖ₑ) ^ (2 : ℝ)
          ∂MeasureTheory.Measure.count)
        ≤ ENNReal.ofReal (C ^ 2) * ∫⁻ x : ℤ, ‖f x‖ₑ ^ (2 : ℝ)
            ∂MeasureTheory.Measure.count := by
    intro f s hf
    have h := hbound f s hf
    simpa only [Lacunary.intervalIntegral_eq_mu01, TLac] using h
  -- Step 1: trigonometric approximations
  have hdense : ∀ m : ℕ, ∃ (s : Finset ℤ) (c : ℤ → ℂ), (∀ n, n ∉ s → c n = 0) ∧
      ∫⁻ θ : ℝ, ‖h θ - Lacunary.trigP s c θ‖ₑ ^ (2 : ℝ) ∂Lacunary.mu01
        ≤ ENNReal.ofReal (1 / ((m : ℝ) + 1)) := by
    intro m
    obtain ⟨s, c, hc, hcl⟩ :=
      Commons.Analysis.ExponentialSums.trigPoly_dense_L2_Ioc h hh
        (ε := 1 / ((m : ℝ) + 1)) (by positivity)
    refine ⟨s, c, hc, ?_⟩
    simpa only [Lacunary.trigP, Lacunary.mu01] using hcl
  choose s c hc0 hclose using hdense
  have hq : ∀ m : ℕ, MemLp (Lacunary.trigP (s m) (c m)) 2 Lacunary.mu01 :=
    fun m => memLp_trigP (s m) (c m)
  -- Step 2: the `L²`-seminorms of the approximations
  have hclose' : ∀ m : ℕ, eLpNorm (fun θ => h θ - Lacunary.trigP (s m) (c m) θ) 2
        Lacunary.mu01 ≤ ENNReal.ofReal (Real.sqrt (1 / ((m : ℝ) + 1))) := by
    intro m
    have hδ : 0 ≤ 1 / ((m : ℝ) + 1) := by positivity
    calc eLpNorm (fun θ => h θ - Lacunary.trigP (s m) (c m) θ) 2 Lacunary.mu01
        = (∫⁻ θ : ℝ, ‖h θ - Lacunary.trigP (s m) (c m) θ‖ₑ ^ (2 : ℝ)
            ∂Lacunary.mu01) ^ (1 / 2 : ℝ) := by
          rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)
            (f := fun θ => h θ - Lacunary.trigP (s m) (c m) θ)
            (hh.aestronglyMeasurable.sub (hq m).aestronglyMeasurable)]
          norm_num
      _ ≤ (ENNReal.ofReal (1 / ((m : ℝ) + 1))) ^ (1 / 2 : ℝ) :=
          ENNReal.rpow_le_rpow (hclose m) (by norm_num)
      _ = ENNReal.ofReal (Real.sqrt (1 / ((m : ℝ) + 1))) := by
          rw [ENNReal.ofReal_rpow_of_nonneg hδ (by norm_num)]
          congr 1
          exact (Real.sqrt_eq_rpow (1 / ((m : ℝ) + 1))).symm
  -- Step 3: `L²`-convergence of the approximations
  have hηlim : Tendsto (fun m : ℕ => Real.sqrt (1 / ((m : ℝ) + 1))) atTop (𝓝 0) := by
    have h1 : Tendsto (fun m : ℕ => (1 : ℝ) / ((m : ℝ) + 1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    have h2 := Real.continuous_sqrt.continuousAt.tendsto.comp h1
    rw [Real.sqrt_zero] at h2
    exact h2
  have hFG : Tendsto (fun m : ℕ => ‖(hq m).toLp - hh.toLp‖) atTop (𝓝 0) := by
    refine squeeze_zero (fun m => norm_nonneg _) (fun m => ?_) hηlim
    calc ‖(hq m).toLp - hh.toLp‖
        = ‖hh.toLp - (hq m).toLp‖ := norm_sub_rev _ _
      _ = (eLpNorm (fun θ => h θ - Lacunary.trigP (s m) (c m) θ) 2 Lacunary.mu01).toReal :=
          norm_toLp_sub_toLp hh (hq m)
      _ ≤ (ENNReal.ofReal (Real.sqrt (1 / ((m : ℝ) + 1)))).toReal :=
          ENNReal.toReal_mono ENNReal.ofReal_ne_top (hclose' m)
      _ = Real.sqrt (1 / ((m : ℝ) + 1)) := ENNReal.toReal_ofReal (Real.sqrt_nonneg _)
  have hFG' : Tendsto (fun m : ℕ => (hq m).toLp) atTop (𝓝 hh.toLp) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    exact hFG
  -- Step 4: the limit of the right-hand sides
  have hGid : ENNReal.ofReal (C ^ 2 * ‖hh.toLp‖ ^ 2)
      = ENNReal.ofReal (C ^ 2) * ∫⁻ θ : ℝ, ‖h θ‖ₑ ^ (2 : ℝ) ∂Lacunary.mu01 := by
    rw [ENNReal.ofReal_mul (sq_nonneg C),
      Commons.Analysis.ExponentialSums.ofReal_norm_sq_eq_lintegral (μ := Lacunary.mu01) hh.toLp]
    congr 1
    refine lintegral_congr_ae ?_
    filter_upwards [MemLp.coeFn_toLp hh] with θ hθ
    rw [hθ]
  have hF3 : Tendsto (fun m : ℕ => ENNReal.ofReal (C ^ 2 * ‖(hq m).toLp‖ ^ 2)) atTop
      (𝓝 (ENNReal.ofReal (C ^ 2) * ∫⁻ θ : ℝ, ‖h θ‖ₑ ^ (2 : ℝ) ∂Lacunary.mu01)) := by
    have hnorm : Tendsto (fun m : ℕ => ‖(hq m).toLp‖) atTop (𝓝 ‖hh.toLp‖) := hFG'.norm
    have hcont : Continuous (fun r : ℝ => ENNReal.ofReal (C ^ 2 * r ^ 2)) :=
      ENNReal.continuous_ofReal.comp (continuous_const.mul (continuous_id.pow 2))
    have hthis := (hcont.tendsto ‖hh.toLp‖).comp hnorm
    rwa [hGid] at hthis
  -- Step 5: pointwise convergence of the individual projections
  have hT : ∀ (i : ℕ) (x : ℤ),
      Tendsto (fun m : ℕ => TLac ρ i x (Lacunary.trigP (s m) (c m))) atTop (𝓝 (TLac ρ i x h)) := by
    intro i x
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero (fun m => norm_nonneg _) (fun m => ?_) hFG
    exact norm_TLac_sub_le ρ i x (hq m) hh
  -- Step 6: the pointwise liminf bound for the maximal functions
  have hsup : ∀ x : ℤ, (⨆ i : ℕ, ‖TLac ρ i x h‖ₑ) ^ (2 : ℝ)
      ≤ Filter.liminf (fun m : ℕ =>
          (⨆ i : ℕ, ‖TLac ρ i x (Lacunary.trigP (s m) (c m))‖ₑ) ^ (2 : ℝ)) atTop := by
    intro x
    have hliminf_i : ∀ i : ℕ,
        Filter.liminf (fun m : ℕ => ‖TLac ρ i x (Lacunary.trigP (s m) (c m))‖ₑ) atTop
          = ‖TLac ρ i x h‖ₑ := fun i => Filter.Tendsto.liminf_eq ((hT i x).enorm)
    have hle : (⨆ i : ℕ, ‖TLac ρ i x h‖ₑ)
        ≤ Filter.liminf (fun m : ℕ =>
            ⨆ i : ℕ, ‖TLac ρ i x (Lacunary.trigP (s m) (c m))‖ₑ) atTop := by
      refine iSup_le fun i => ?_
      rw [← hliminf_i i]
      exact Filter.liminf_le_liminf (Filter.Eventually.of_forall (fun m =>
        le_iSup (fun i : ℕ => ‖TLac ρ i x (Lacunary.trigP (s m) (c m))‖ₑ) i))
    calc (⨆ i : ℕ, ‖TLac ρ i x h‖ₑ) ^ (2 : ℝ)
        ≤ (Filter.liminf (fun m : ℕ =>
            ⨆ i : ℕ, ‖TLac ρ i x (Lacunary.trigP (s m) (c m))‖ₑ) atTop) ^ (2 : ℝ) :=
          ENNReal.rpow_le_rpow hle (by norm_num)
      _ ≤ Filter.liminf (fun m : ℕ =>
            (⨆ i : ℕ, ‖TLac ρ i x (Lacunary.trigP (s m) (c m))‖ₑ) ^ (2 : ℝ)) atTop :=
          liminf_rpow_two_le
  -- Step 7: the polynomial bound at each scale
  have hbm : ∀ m : ℕ, (∫⁻ x : ℤ,
        (⨆ i : ℕ, ‖TLac ρ i x (Lacunary.trigP (s m) (c m))‖ₑ) ^ (2 : ℝ)
        ∂MeasureTheory.Measure.count) ≤ ENNReal.ofReal (C ^ 2 * ‖(hq m).toLp‖ ^ 2) := by
    intro m
    have hb := hbound' (c m) (s m) (hc0 m)
    have h1 : (∫⁻ x : ℤ, ‖c m x‖ₑ ^ (2 : ℝ) ∂MeasureTheory.Measure.count)
        = ENNReal.ofReal (∑ j ∈ s m, ‖c m j‖ ^ 2) :=
      Lacunary.f_lintegral (s m) (c m) (hc0 m)
    have h2 : ENNReal.ofReal (∑ j ∈ s m, ‖c m j‖ ^ 2)
        = ENNReal.ofReal (‖(hq m).toLp‖ ^ 2) := by
      rw [← Lacunary.trig_lintegral (s m) (c m),
        Commons.Analysis.ExponentialSums.ofReal_norm_sq_eq_lintegral (μ := Lacunary.mu01)
          ((hq m).toLp)]
      refine lintegral_congr_ae ?_
      filter_upwards [MemLp.coeFn_toLp (hq m)] with θ hθ
      rw [hθ]
    calc (∫⁻ x : ℤ, (⨆ i : ℕ, ‖TLac ρ i x (Lacunary.trigP (s m) (c m))‖ₑ) ^ (2 : ℝ)
          ∂MeasureTheory.Measure.count)
        ≤ ENNReal.ofReal (C ^ 2) * ∫⁻ x : ℤ, ‖c m x‖ₑ ^ (2 : ℝ)
            ∂MeasureTheory.Measure.count := hb
      _ = ENNReal.ofReal (C ^ 2) * ENNReal.ofReal (‖(hq m).toLp‖ ^ 2) := by rw [h1, h2]
      _ = ENNReal.ofReal (C ^ 2 * ‖(hq m).toLp‖ ^ 2) := by
          rw [← ENNReal.ofReal_mul (sq_nonneg C)]
  -- Step 8: Fatou
  have key : (∫⁻ x : ℤ, (⨆ i : ℕ, ‖TLac ρ i x h‖ₑ) ^ (2 : ℝ) ∂MeasureTheory.Measure.count)
      ≤ ENNReal.ofReal (C ^ 2) * ∫⁻ θ : ℝ, ‖h θ‖ₑ ^ (2 : ℝ) ∂Lacunary.mu01 := by
    calc (∫⁻ x : ℤ, (⨆ i : ℕ, ‖TLac ρ i x h‖ₑ) ^ (2 : ℝ) ∂MeasureTheory.Measure.count)
        ≤ ∫⁻ x : ℤ, Filter.liminf (fun m : ℕ =>
            (⨆ i : ℕ, ‖TLac ρ i x (Lacunary.trigP (s m) (c m))‖ₑ) ^ (2 : ℝ)) atTop
            ∂MeasureTheory.Measure.count := lintegral_mono hsup
      _ ≤ Filter.liminf (fun m : ℕ => ∫⁻ x : ℤ,
            (⨆ i : ℕ, ‖TLac ρ i x (Lacunary.trigP (s m) (c m))‖ₑ) ^ (2 : ℝ)
            ∂MeasureTheory.Measure.count) atTop :=
          lintegral_liminf_le' (fun m => (measurable_of_countable _).aemeasurable)
      _ ≤ Filter.liminf (fun m : ℕ => ENNReal.ofReal (C ^ 2 * ‖(hq m).toLp‖ ^ 2)) atTop :=
          Filter.liminf_le_liminf (Filter.Eventually.of_forall hbm)
      _ = ENNReal.ofReal (C ^ 2) * ∫⁻ θ : ℝ, ‖h θ‖ₑ ^ (2 : ℝ) ∂Lacunary.mu01 :=
          Filter.Tendsto.liminf_eq hF3
  simpa only [Lacunary.intervalIntegral_eq_mu01, TLac] using key

end

end Work.BourgainPlan.Oscillation
