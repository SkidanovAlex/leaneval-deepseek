/-
Work.MRMT.Found — the camp-neutral "forward limit" layer of the measurable Riemann mapping
theorem.

This file is a **camp-neutral** production of the forward-limit theorem: it proves the same
statement as `Work.MRMT.Found.forward_limit_lp` (and hence as
`Work.MRMT.Found.forward_limit_clean`), but it does not import
`Work.MRMT.QC.principal_unique`.  The only ingredient of `forward_limit_lp` that lived in that
module is the identity `∂F - 1 = S (∂̄F)`; here we use the re-proof
`Work.MRMT.Found.dz_sub_one_eq_beurlingL2_pd` from `Found/principalData_aux`, which is stated
and proved without `Work.MRMT.QC.principal_unique`.

This matters because two modules in the workspace, `Work.MRMT.QC.principal_unique` and
`Work.MRMT.QC.eq_zero_of_beltrami_of_decay`, both declare the name
`Work.MRMT.QC.eq_zero_of_beltrami_of_decay` (with different signatures); no module can import
both.  The `principalData_exists` assembly needs the smooth Ahlfors–Bers theorem
(`Work.MRMT.Found.exists_contDiff_principal_of_contDiff`), which lives on the
`eq_zero_of_beltrami_of_decay` side, so its forward limit is produced here.

Given

* smooth compactly supported Beltrami coefficients `μn n` with `‖μn n‖ ≤ k < 1` everywhere and
  `μn n z ≠ 0 → ‖z‖ ≤ M` (a *uniform* support radius),
* `μn n → μ` a.e. with `‖μ‖ ≤ k` a.e., and
* `C¹` homeomorphisms `Fn n` of `ℂ` solving `∂̄(Fn n) = μn n · ∂(Fn n)` with the normalisation
  `Fn n z - z = O(1/‖z‖)`,

there is a continuous limit `φ` of the `Fn n` (locally uniformly), a limit `D` of the Wirtinger
derivatives `∂(Fn n)` (in `L²` on compacta) and *uniform* decay constants `Cd, Rd` valid for
every `Fn n` and for `φ`.
-/
import Mathlib
import Submission.Work.MRMT.Found.Defs
import Submission.Work.MRMT.Found.hsolA_spec
import Submission.Work.MRMT.Found.isDzDeriv_cauchyTransform_eq_beurlingL2
import Submission.Work.MRMT.Found.sub_id_ae_eq_cauchyTransform_dzbar
import Submission.Work.MRMT.Found.continuous_cauchyTransform_of_memLp
import Submission.Work.MRMT.Found.courantLebesgue_uniform
import Submission.Work.MRMT.Found.exists_tendstoLocallyUniformly_of_l2_of_modulus
import Submission.Work.MRMT.Found.cauchyTransform_memLp_ball
import Submission.Work.MRMT.Found.principalData_aux
import Submission.Work.MRMT.Beltrami.energy_identity
import Submission.Work.MRMT.Weyl.Defs
import Submission.Work.MRMT.Found.fw_memLp_dzbar
import Submission.Work.MRMT.Found.fw_ae_eq_hsolA_of_ae_eq_mul_one_add
import Submission.Work.MRMT.Found.fw_admissible_of_tendsto_ae
import Submission.Work.MRMT.Found.fw_decay_cauchyTransform_le
import Submission.Work.MRMT.Found.fw_integral_normSq_cauchyTransform_le
import Submission.Work.MRMT.Found.fw_exists_uniform_modulus
import Submission.Work.MRMT.Found.fw_volume_image_ball_le
import Submission.Work.MRMT.Cauchy.integrable_cauchyKernel_of_memLp

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.MRMT.Found

open MeasureTheory Filter Topology Complex Function
open scoped Distributions Topology ENNReal

/-! ## Glue: the pointwise Cauchy-transform representation -/

/-- A continuous function on `ℂ` is determined by its a.e. values. -/
theorem fpd_eq_of_ae_eq_of_continuous {f g : ℂ → ℂ} (hf : Continuous f) (hg : Continuous g)
    (h : f =ᵐ[(volume : Measure ℂ)] g) : f = g :=
  (Continuous.ae_eq_iff_eq (volume : Measure ℂ) hf hg).mp h

/-- `F z - z = C(∂̄F) z` for *every* `z`, when `F` is `C¹`, `∂̄F` is compactly supported and
`F z - z = O(1/‖z‖)`. -/
theorem fpd_sub_id_eq_cauchyTransform_dzbar {F : ℂ → ℂ} (hF : ContDiff ℝ 1 F)
    (hs : HasCompactSupport (fun z => dzbar F z))
    (hdec : ∃ C R : ℝ, ∀ z : ℂ, R ≤ ‖z‖ → ‖F z - z‖ ≤ C / ‖z‖) :
    ∀ z : ℂ, F z - z = cauchyTransform (fun w => dzbar F w) z := by
  have hdb : Continuous (fun z => dzbar F z) :=
    Weyl.continuous_dzbar_of_contDiff hF (by norm_num)
  have hLp3 : MemLp (fun z => dzbar F z) 3 (volume : Measure ℂ) :=
    hdb.memLp_of_hasCompactSupport hs
  have hcont : Continuous (cauchyTransform (fun w => dzbar F w)) :=
    continuous_cauchyTransform_of_memLp (p := 3) (by norm_num) hLp3 hs
  have hae := sub_id_ae_eq_cauchyTransform_dzbar hF hs hdec
  have hfun : (fun z => F z - z) = cauchyTransform (fun w => dzbar F w) :=
    fpd_eq_of_ae_eq_of_continuous (hF.continuous.sub continuous_id) hcont hae
  intro z
  exact congrFun hfun z

/-- The Cauchy transform is additive on compactly supported `L^p` (`p > 2`) functions. -/
theorem fpd_cauchyTransform_sub {f g : ℂ → ℂ} {p : ℝ≥0∞} (hp : 2 < p)
    (hf : MemLp f p (volume : Measure ℂ)) (hfs : HasCompactSupport f)
    (hg : MemLp g p (volume : Measure ℂ)) (hgs : HasCompactSupport g) (z : ℂ) :
    cauchyTransform (fun ζ => f ζ - g ζ) z = cauchyTransform f z - cauchyTransform g z := by
  have hfi : Integrable (fun w => f w / (w - z)) (volume : Measure ℂ) :=
    Work.MRMT.Cauchy.integrable_cauchyKernel_of_memLp hp hf hfs z
  have hgi : Integrable (fun w => g w / (w - z)) (volume : Measure ℂ) :=
    Work.MRMT.Cauchy.integrable_cauchyKernel_of_memLp hp hg hgs z
  have hcongr : (fun w => (f w - g w) / (w - z))
      = fun w => f w / (w - z) - g w / (w - z) := by
    funext w
    rw [sub_div]
  rw [cauchyTransform, cauchyTransform, cauchyTransform, hcongr, integral_sub hfi hgi, mul_sub]

/-! ## `L²`-norm identities -/

/-- For an `L²` class, the squared `L²` norm is the integral of the squared norm of a
representative. -/
theorem fpd_norm_sq_Lp (g : Lp ℂ 2 (volume : Measure ℂ)) :
    ∫ z, ‖(g : ℂ → ℂ) z‖ ^ 2 = ‖g‖ ^ 2 := by
  have h := Work.MRMT.Beltrami.integral_norm_sq_eq_toLp_norm_sq (g : ℂ → ℂ) (Lp.memLp g)
  rwa [Lp.toLp_coeFn g (Lp.memLp g)] at h

/-- The `L²` norm of `toLp` of a function bounded by `k` and supported in `closedBall 0 M`. -/
theorem fpd_norm_toLp_le {μ : ℂ → ℂ} {k M : ℝ} (hk0 : 0 ≤ k)
    (hLp : MemLp μ 2 (volume : Measure ℂ))
    (hμb : ∀ᵐ z ∂(volume : Measure ℂ), ‖μ z‖ ≤ k)
    (hμs : ∀ z : ℂ, μ z ≠ 0 → ‖z‖ ≤ M) :
    ‖hLp.toLp μ‖ ≤ k * Real.sqrt ((volume (Metric.closedBall (0 : ℂ) M)).toReal) := by
  have hVnn : 0 ≤ (volume (Metric.closedBall (0 : ℂ) M)).toReal := ENNReal.toReal_nonneg
  have hsupp : ∀ z ∉ Metric.closedBall (0 : ℂ) M, μ z = 0 := by
    intro z hz
    by_contra hne
    exact absurd (hμs z hne) (by simpa [Metric.mem_closedBall] using hz)
  have hμsq : ∫ z, ‖μ z‖ ^ 2
      ≤ k ^ 2 * (volume (Metric.closedBall (0 : ℂ) M)).toReal := by
    have hμInt : Integrable (fun z => ‖μ z‖ ^ 2) (volume : Measure ℂ) :=
      (memLp_two_iff_integrable_sq_norm hLp.aestronglyMeasurable).1 hLp
    have hμOn : IntegrableOn (fun z => ‖μ z‖ ^ 2) (Metric.closedBall (0 : ℂ) M)
        (volume : Measure ℂ) := hμInt.integrableOn
    have hcOn : IntegrableOn (fun _ : ℂ => k ^ 2) (Metric.closedBall (0 : ℂ) M)
        (volume : Measure ℂ) :=
      integrableOn_const (isCompact_closedBall (0 : ℂ) M).measure_lt_top.ne (by simp)
    have hle : ∫ z in Metric.closedBall (0 : ℂ) M, ‖μ z‖ ^ 2
        ≤ ∫ z in Metric.closedBall (0 : ℂ) M, k ^ 2 := by
      refine setIntegral_mono_ae hμOn hcOn ?_
      filter_upwards [hμb] with z hz
      exact pow_le_pow_left₀ (norm_nonneg _) hz 2
    rw [setIntegral_const, Measure.real_def, smul_eq_mul] at hle
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := Metric.closedBall (0 : ℂ) M)
      (f := fun z => ‖μ z‖ ^ 2) (fun z hz => by rw [hsupp z hz]; simp)]
    simpa [mul_comm] using hle
  have h1 : ‖hLp.toLp μ‖ ^ 2
      ≤ (k * Real.sqrt ((volume (Metric.closedBall (0 : ℂ) M)).toReal)) ^ 2 := by
    calc ‖hLp.toLp μ‖ ^ 2
        = ∫ z, ‖(hLp.toLp μ : ℂ → ℂ) z‖ ^ 2 := (fpd_norm_sq_Lp _).symm
      _ = ∫ z, ‖μ z‖ ^ 2 :=
          integral_congr_ae ((MemLp.coeFn_toLp hLp).mono (fun z hz => by dsimp only; rw [hz]))
      _ ≤ k ^ 2 * (volume (Metric.closedBall (0 : ℂ) M)).toReal := hμsq
      _ = (k * Real.sqrt ((volume (Metric.closedBall (0 : ℂ) M)).toReal)) ^ 2 := by
          rw [mul_pow, Real.sq_sqrt hVnn]
  have h2 := Real.sqrt_le_sqrt h1
  rwa [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq (by positivity)] at h2

/-- Every Ahlfors–Bers solution for a coefficient supported in `closedBall 0 M` and bounded by
`k < 1` a.e. has `L²` norm at most `k √(vol (closedBall 0 M)) / (1 - k)`. -/
theorem fpd_hsolA_norm_le {μ : ℂ → ℂ} {k M : ℝ} (hk0 : 0 ≤ k) (hk1 : k < 1)
    (hAdm : Admissible μ) (hLp : MemLp μ 2 (volume : Measure ℂ))
    (hμb : ∀ᵐ z ∂(volume : Measure ℂ), ‖μ z‖ ≤ k)
    (hμs : ∀ z : ℂ, μ z ≠ 0 → ‖z‖ ≤ M) :
    ‖hsolA μ hAdm hLp‖
      ≤ k * Real.sqrt ((volume (Metric.closedBall (0 : ℂ) M)).toReal) / (1 - k) := by
  obtain ⟨-, hbound, -⟩ := hsolA_spec hAdm hLp hk1 hμb
  have hk1pos : 0 < 1 - k := by linarith
  rw [inv_mul_eq_div] at hbound
  exact hbound.trans (div_le_div_of_nonneg_right (fpd_norm_toLp_le hk0 hLp hμb hμs) hk1pos.le)

/-! ## The resolvent identity and the stability of `hsolA` -/

/-- `mulL2 μ` is bounded by `k` when `‖μ‖ ≤ k` a.e. -/
theorem fpd_mulL2_norm_le_mul {μ : ℂ → ℂ} (hm : AEStronglyMeasurable μ (volume : Measure ℂ))
    (h1 : ∀ᵐ z ∂(volume : Measure ℂ), ‖μ z‖ ≤ 1) {k : ℝ}
    (hb : ∀ᵐ z ∂(volume : Measure ℂ), ‖μ z‖ ≤ k) (g : Lp ℂ 2 (volume : Measure ℂ)) :
    ‖mulL2 μ hm h1 g‖ ≤ k * ‖g‖ := by
  refine Lp.norm_le_mul_norm_of_ae_le_mul (c := k) ?_
  filter_upwards [mulL2_apply_ae μ hm h1 g, hb] with z hz hkz
  rw [hz, norm_mul]
  exact mul_le_mul_of_nonneg_right hkz (norm_nonneg _)

/-- The resolvent identity `hsolA μ = toLp μ + M_μ (S (hsolA μ))`. -/
theorem fpd_hsolA_resolvent {μ : ℂ → ℂ} (hμ : Admissible μ) (hLp : MemLp μ 2 (volume : Measure ℂ))
    {k : ℝ} (hk : k < 1) (hb : ∀ᵐ z ∂(volume : Measure ℂ), ‖μ z‖ ≤ k)
    (hb1 : ∀ᵐ z ∂(volume : Measure ℂ), ‖μ z‖ ≤ 1) :
    hsolA μ hμ hLp
      = hLp.toLp μ + ((mulL2 μ hμ.meas hb1).comp beurlingL2) (hsolA μ hμ hLp) := by
  rw [Lp.ext_iff]
  have hspec := (hsolA_spec hμ hLp hk hb).1
  have h2 := Lp.coeFn_add (hLp.toLp μ)
    (((mulL2 μ hμ.meas hb1).comp beurlingL2) (hsolA μ hμ hLp))
  have h3 := mulL2_apply_ae μ hμ.meas hb1 (beurlingL2 (hsolA μ hμ hLp))
  have h4 := MemLp.coeFn_toLp hLp
  filter_upwards [hspec, h2, h3, h4] with z hz1 hz2 hz3 hz4
  simp only [ContinuousLinearMap.comp_apply, Pi.add_apply] at hz2 ⊢
  rw [hz2, hz3, hz4, hz1]
  ring

/-- Dominated convergence: `∫ ‖μn n - μ'‖² → 0` for a uniformly bounded family with a common
support radius converging a.e. -/
theorem fpd_tendsto_integral_normSq_sub_of_tendsto_ae_bound
    {μ' : ℂ → ℂ} {μn : ℕ → ℂ → ℂ} {k M : ℝ}
    (hmeas' : AEStronglyMeasurable μ' (volume : Measure ℂ))
    (hmeasn : ∀ n, AEStronglyMeasurable (μn n) (volume : Measure ℂ))
    (hb' : ∀ᵐ z ∂(volume : Measure ℂ), ‖μ' z‖ ≤ k)
    (hbn : ∀ n, ∀ᵐ z ∂(volume : Measure ℂ), ‖μn n z‖ ≤ k)
    (hMn : ∀ n, ∀ z : ℂ, μn n z ≠ 0 → ‖z‖ ≤ M)
    (hM' : ∀ z : ℂ, M < ‖z‖ → μ' z = 0)
    (hconv : ∀ᵐ z ∂(volume : Measure ℂ),
      Tendsto (fun n => μn n z) atTop (𝓝 (μ' z))) :
    Tendsto (fun n => ∫ z, ‖μn n z - μ' z‖ ^ 2) atTop (𝓝 0) := by
  set s : Set ℂ := Metric.closedBall 0 M with hsdef
  have hsmeas : MeasurableSet s := measurableSet_closedBall
  have hfin : (volume : Measure ℂ) s ≠ ∞ :=
    (isCompact_closedBall (0 : ℂ) M).measure_lt_top.ne
  have hind : Integrable (s.indicator (fun _ => (1 : ℝ))) (volume : Measure ℂ) :=
    (integrable_indicator_iff hsmeas).2 (integrableOn_const hfin (by simp))
  have hF_meas : ∀ n, AEStronglyMeasurable (fun z : ℂ => ‖μn n z - μ' z‖ ^ 2)
      (volume : Measure ℂ) := fun n => ((hmeasn n).sub hmeas').norm.pow 2
  have hbound_int : Integrable (fun z : ℂ => (2 * k) ^ 2 * s.indicator (fun _ => (1 : ℝ)) z)
      (volume : Measure ℂ) := hind.const_mul _
  have h_bound : ∀ n, ∀ᵐ z ∂(volume : Measure ℂ),
      ‖‖μn n z - μ' z‖ ^ 2‖ ≤ (2 * k) ^ 2 * s.indicator (fun _ => (1 : ℝ)) z := by
    intro n
    filter_upwards [hbn n, hb'] with z hzk hz'k
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    by_cases hz : z ∈ s
    · have h1 : ‖μn n z - μ' z‖ ≤ 2 * k := by
        calc ‖μn n z - μ' z‖ ≤ ‖μn n z‖ + ‖μ' z‖ := norm_sub_le _ _
          _ ≤ k + k := add_le_add hzk hz'k
          _ = 2 * k := by ring
      have h2 : ‖μn n z - μ' z‖ ^ 2 ≤ (2 * k) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
      simpa [Set.indicator_of_mem hz] using h2
    · have hzM : M < ‖z‖ := by
        have : ¬ (dist z 0 ≤ M) := by
          intro h
          exact hz (by rw [hsdef, Metric.mem_closedBall]; exact h)
        rw [dist_zero_right] at this
        exact lt_of_not_ge this
      have hμ'0 : μ' z = 0 := hM' z hzM
      have hμn0 : μn n z = 0 := by
        by_contra hne
        exact absurd (hMn n z hne) (not_le.mpr hzM)
      simp [Set.indicator_of_notMem hz, hμn0, hμ'0]
  have h_lim : ∀ᵐ z ∂(volume : Measure ℂ),
      Tendsto (fun n => ‖μn n z - μ' z‖ ^ 2) atTop (𝓝 ((fun _ : ℂ => (0 : ℝ)) z)) := by
    filter_upwards [hconv] with z hz
    have h2 : Tendsto (fun n => μn n z - μ' z) atTop (𝓝 0) := by
      have h1 : Tendsto (fun n => μn n z - μ' z) atTop (𝓝 (μ' z - μ' z)) :=
        hz.sub tendsto_const_nhds
      simpa using h1
    simpa using h2.norm.pow 2
  have hmain := MeasureTheory.tendsto_integral_of_dominated_convergence
    (μ := (volume : Measure ℂ)) (F := fun n z => ‖μn n z - μ' z‖ ^ 2)
    (f := fun _ : ℂ => (0 : ℝ))
    (fun z => (2 * k) ^ 2 * s.indicator (fun _ => (1 : ℝ)) z) hF_meas hbound_int h_bound h_lim
  simpa using hmain

/-- Dominated convergence: `∫ ‖(μn n - μ') · w‖² → 0` for any fixed `w ∈ L²`. -/
theorem fpd_tendsto_integral_normSq_sub_mul_of_tendsto_ae_bound
    {μ' : ℂ → ℂ} {μn : ℕ → ℂ → ℂ} {k : ℝ}
    (hmeas' : AEStronglyMeasurable μ' (volume : Measure ℂ))
    (hmeasn : ∀ n, AEStronglyMeasurable (μn n) (volume : Measure ℂ))
    (hb' : ∀ᵐ z ∂(volume : Measure ℂ), ‖μ' z‖ ≤ k)
    (hbn : ∀ n, ∀ᵐ z ∂(volume : Measure ℂ), ‖μn n z‖ ≤ k)
    (hconv : ∀ᵐ z ∂(volume : Measure ℂ),
      Tendsto (fun n => μn n z) atTop (𝓝 (μ' z)))
    {w : ℂ → ℂ} (hw : MemLp w 2 (volume : Measure ℂ)) :
    Tendsto (fun n => ∫ z, ‖(μn n z - μ' z) * w z‖ ^ 2) atTop (𝓝 0) := by
  have hwi : Integrable (fun z => ‖w z‖ ^ 2) (volume : Measure ℂ) :=
    (memLp_two_iff_integrable_sq_norm hw.aestronglyMeasurable).1 hw
  have hF_meas : ∀ n, AEStronglyMeasurable (fun z : ℂ => ‖(μn n z - μ' z) * w z‖ ^ 2)
      (volume : Measure ℂ) :=
    fun n => (((hmeasn n).sub hmeas').mul hw.aestronglyMeasurable).norm.pow 2
  have hbound_int : Integrable (fun z : ℂ => (2 * k) ^ 2 * ‖w z‖ ^ 2) (volume : Measure ℂ) :=
    hwi.const_mul _
  have h_bound : ∀ n, ∀ᵐ z ∂(volume : Measure ℂ),
      ‖‖(μn n z - μ' z) * w z‖ ^ 2‖ ≤ (2 * k) ^ 2 * ‖w z‖ ^ 2 := by
    intro n
    filter_upwards [hbn n, hb'] with z hzk hz'k
    rw [Real.norm_of_nonneg (sq_nonneg _), norm_mul, mul_pow]
    have h1 : ‖μn n z - μ' z‖ ≤ 2 * k := by
      calc ‖μn n z - μ' z‖ ≤ ‖μn n z‖ + ‖μ' z‖ := norm_sub_le _ _
        _ ≤ k + k := add_le_add hzk hz'k
        _ = 2 * k := by ring
    have h2 : ‖μn n z - μ' z‖ ^ 2 ≤ (2 * k) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
    exact mul_le_mul_of_nonneg_right h2 (sq_nonneg _)
  have h_lim : ∀ᵐ z ∂(volume : Measure ℂ),
      Tendsto (fun n => ‖(μn n z - μ' z) * w z‖ ^ 2) atTop (𝓝 ((fun _ : ℂ => (0 : ℝ)) z)) := by
    filter_upwards [hconv] with z hz
    have h1 : Tendsto (fun n => μn n z - μ' z) atTop (𝓝 0) := by
      have h0 : Tendsto (fun n => μn n z - μ' z) atTop (𝓝 (μ' z - μ' z)) :=
        hz.sub tendsto_const_nhds
      simpa using h0
    have h3 : Tendsto (fun n => (μn n z - μ' z) * w z) atTop (𝓝 0) := by
      have h2 : Tendsto (fun n => (μn n z - μ' z) * w z) atTop (𝓝 (0 * w z)) :=
        h1.mul tendsto_const_nhds
      simpa using h2
    simpa using h3.norm.pow 2
  have hmain := MeasureTheory.tendsto_integral_of_dominated_convergence
    (μ := (volume : Measure ℂ)) (F := fun n z => ‖(μn n z - μ' z) * w z‖ ^ 2)
    (f := fun _ : ℂ => (0 : ℝ))
    (fun z => (2 * k) ^ 2 * ‖w z‖ ^ 2) hF_meas hbound_int h_bound h_lim
  simpa using hmain

/-- **Stability of `hsolA` in the coefficient.**  For uniformly bounded coefficients `μn → μ'`
a.e. with a common support radius, the Ahlfors–Bers solutions converge in `L²`. -/
theorem fpd_hsolA_tendsto {μ' : ℂ → ℂ} {μn : ℕ → ℂ → ℂ} {k M : ℝ}
    (hk0 : 0 ≤ k) (hk1 : k < 1)
    (hAdm' : Admissible μ') (hLp' : MemLp μ' 2 (volume : Measure ℂ))
    (hAdmn : ∀ n, Admissible (μn n)) (hLpn : ∀ n, MemLp (μn n) 2 (volume : Measure ℂ))
    (hbn : ∀ n, ∀ᵐ z ∂(volume : Measure ℂ), ‖μn n z‖ ≤ k)
    (hb' : ∀ᵐ z ∂(volume : Measure ℂ), ‖μ' z‖ ≤ k)
    (hMn : ∀ n, ∀ z : ℂ, μn n z ≠ 0 → ‖z‖ ≤ M)
    (hM' : ∀ z : ℂ, M < ‖z‖ → μ' z = 0)
    (hconv : ∀ᵐ z ∂(volume : Measure ℂ),
      Tendsto (fun n => μn n z) atTop (𝓝 (μ' z))) :
    Tendsto (fun n => ‖hsolA (μn n) (hAdmn n) (hLpn n) - hsolA μ' hAdm' hLp'‖)
      atTop (𝓝 0) := by
  have hk1pos : 0 < 1 - k := by linarith
  have h1n : ∀ n, ∀ᵐ z ∂(volume : Measure ℂ), ‖μn n z‖ ≤ 1 := fun n => by
    filter_upwards [hbn n] with z hz
    linarith [norm_nonneg (μn n z)]
  have h1' : ∀ᵐ z ∂(volume : Measure ℂ), ‖μ' z‖ ≤ 1 := by
    filter_upwards [hb'] with z hz
    linarith [norm_nonneg (μ' z)]
  have hD1 : Tendsto (fun n => ∫ z, ‖μn n z - μ' z‖ ^ 2) atTop (𝓝 0) :=
    fpd_tendsto_integral_normSq_sub_of_tendsto_ae_bound hAdm'.meas (fun n => (hAdmn n).meas)
      hb' hbn hMn hM' hconv
  have hw : MemLp ((beurlingL2 (hsolA μ' hAdm' hLp') :
      Lp ℂ 2 (volume : Measure ℂ)) : ℂ → ℂ) 2 (volume : Measure ℂ) := Lp.memLp _
  have hD2 : Tendsto (fun n => ∫ z, ‖(μn n z - μ' z) * ((beurlingL2 (hsolA μ' hAdm' hLp') :
      Lp ℂ 2 (volume : Measure ℂ)) : ℂ → ℂ) z‖ ^ 2) atTop (𝓝 0) :=
    fpd_tendsto_integral_normSq_sub_mul_of_tendsto_ae_bound hAdm'.meas (fun n => (hAdmn n).meas)
      hb' hbn hconv hw
  have hbound : ∀ n, ‖hsolA (μn n) (hAdmn n) (hLpn n) - hsolA μ' hAdm' hLp'‖
      ≤ (1 - k)⁻¹ * (Real.sqrt (∫ z, ‖μn n z - μ' z‖ ^ 2)
        + Real.sqrt (∫ z, ‖(μn n z - μ' z) * ((beurlingL2 (hsolA μ' hAdm' hLp') :
            Lp ℂ 2 (volume : Measure ℂ)) : ℂ → ℂ) z‖ ^ 2)) := by
    intro n
    set Tn : Lp ℂ 2 (volume : Measure ℂ) →L[ℂ] Lp ℂ 2 (volume : Measure ℂ) :=
      (mulL2 (μn n) (hAdmn n).meas (h1n n)).comp beurlingL2
    set T' : Lp ℂ 2 (volume : Measure ℂ) →L[ℂ] Lp ℂ 2 (volume : Measure ℂ) :=
      (mulL2 μ' hAdm'.meas h1').comp beurlingL2
    have hresn : hsolA (μn n) (hAdmn n) (hLpn n)
        = (hLpn n).toLp (μn n) + Tn (hsolA (μn n) (hAdmn n) (hLpn n)) :=
      fpd_hsolA_resolvent (hAdmn n) (hLpn n) hk1 (hbn n) (h1n n)
    have hres' : hsolA μ' hAdm' hLp'
        = hLp'.toLp μ' + T' (hsolA μ' hAdm' hLp') :=
      fpd_hsolA_resolvent hAdm' hLp' hk1 hb' h1'
    set An : Lp ℂ 2 (volume : Measure ℂ) := hsolA (μn n) (hAdmn n) (hLpn n) with hAndef
    set B : Lp ℂ 2 (volume : Measure ℂ) := hsolA μ' hAdm' hLp' with hBdef
    have key : An - B = ((hLpn n).toLp (μn n) - hLp'.toLp μ') + Tn (An - B) + (Tn - T') B := by
      have e1 : Tn (An - B) = Tn An - Tn B := map_sub Tn An B
      have e2 : (Tn - T') B = Tn B - T' B := ContinuousLinearMap.sub_apply Tn T' B
      conv_lhs => rw [hresn, hres']
      rw [e1, e2]
      abel
    have h1le : ‖An - B‖ ≤ ‖(hLpn n).toLp (μn n) - hLp'.toLp μ'‖ + k * ‖An - B‖
        + ‖(Tn - T') B‖ := by
      have h := norm_add₃_le (a := (hLpn n).toLp (μn n) - hLp'.toLp μ')
        (b := Tn (An - B)) (c := (Tn - T') B)
      have hk' : ‖Tn (An - B)‖ ≤ k * ‖An - B‖ := by
        have hunf : Tn = (mulL2 (μn n) (hAdmn n).meas (h1n n)).comp beurlingL2 := rfl
        rw [hunf, ContinuousLinearMap.comp_apply]
        refine (fpd_mulL2_norm_le_mul (hAdmn n).meas (h1n n) (hbn n)
          (beurlingL2 (An - B))).trans ?_
        rw [norm_beurlingL2]
      have h' : ‖An - B‖
          = ‖((hLpn n).toLp (μn n) - hLp'.toLp μ') + Tn (An - B) + (Tn - T') B‖ :=
        congrArg norm key
      have h2 : ‖An - B‖
          ≤ ‖(hLpn n).toLp (μn n) - hLp'.toLp μ'‖ + ‖Tn (An - B)‖ + ‖(Tn - T') B‖ := by
        conv_lhs => rw [h']
        exact h
      linarith [h2, hk']
    have h2le : (1 - k) * ‖An - B‖
        ≤ ‖(hLpn n).toLp (μn n) - hLp'.toLp μ'‖ + ‖(Tn - T') B‖ := by
      have h3 : (1 - k) * ‖An - B‖ = ‖An - B‖ - k * ‖An - B‖ := by ring
      rw [h3]
      linarith [h1le]
    have hA : ‖(hLpn n).toLp (μn n) - hLp'.toLp μ'‖
        = Real.sqrt (∫ z, ‖μn n z - μ' z‖ ^ 2) := by
      have hMem : MemLp (fun z => μn n z - μ' z) 2 (volume : Measure ℂ) := (hLpn n).sub hLp'
      have htoLp : (hLpn n).toLp (μn n) - hLp'.toLp μ'
          = hMem.toLp (fun z => μn n z - μ' z) := (MemLp.toLp_sub (hLpn n) hLp').symm
      have hnorm : ‖hMem.toLp (fun z => μn n z - μ' z)‖ ^ 2
          = ∫ z, ‖μn n z - μ' z‖ ^ 2 := by
        rw [← fpd_norm_sq_Lp]
        apply integral_congr_ae
        exact (MemLp.coeFn_toLp hMem).mono (fun z hz => by dsimp only; rw [hz])
      calc ‖(hLpn n).toLp (μn n) - hLp'.toLp μ'‖
          = ‖hMem.toLp (fun z => μn n z - μ' z)‖ := by rw [htoLp]
        _ = Real.sqrt (∫ z, ‖μn n z - μ' z‖ ^ 2) := by
            rw [← hnorm, Real.sqrt_sq (norm_nonneg _)]
    have hB2 : ‖(Tn - T') B‖
        = Real.sqrt (∫ z, ‖(μn n z - μ' z) * ((beurlingL2 B :
            Lp ℂ 2 (volume : Measure ℂ)) : ℂ → ℂ) z‖ ^ 2) := by
      have hsub : ((Tn - T') B : Lp ℂ 2 (volume : Measure ℂ)) = Tn B - T' B :=
        ContinuousLinearMap.sub_apply Tn T' B
      have hae : (Tn B - T' B : Lp ℂ 2 (volume : Measure ℂ))
          =ᵐ[(volume : Measure ℂ)] fun z => (μn n z - μ' z)
            * ((beurlingL2 B : Lp ℂ 2 (volume : Measure ℂ)) : ℂ → ℂ) z := by
        filter_upwards [Lp.coeFn_sub (Tn B) (T' B),
          mulL2_apply_ae (μn n) (hAdmn n).meas (h1n n) (beurlingL2 B),
          mulL2_apply_ae μ' hAdm'.meas h1' (beurlingL2 B)] with z h1 h2 h3
        rw [h1]
        simp only [Pi.sub_apply]
        dsimp only [Tn, T']
        simp only [ContinuousLinearMap.comp_apply]
        rw [h2, h3]
        ring
      have hnorm : ‖(Tn - T') B‖ ^ 2
          = ∫ z, ‖(μn n z - μ' z) * ((beurlingL2 B :
              Lp ℂ 2 (volume : Measure ℂ)) : ℂ → ℂ) z‖ ^ 2 := by
        rw [← fpd_norm_sq_Lp, hsub]
        apply integral_congr_ae
        exact hae.mono (fun z hz => by dsimp only; rw [hz])
      rw [← hnorm, Real.sqrt_sq (norm_nonneg _)]
    rw [hB2] at h2le
    rw [hA] at h2le
    rw [hAndef, hBdef] at h2le
    rw [inv_mul_eq_div, le_div_iff₀ hk1pos]
    linarith [h2le, mul_comm (1 - k) ‖hsolA (μn n) (hAdmn n) (hLpn n) - hsolA μ' hAdm' hLp'‖]
  have h1 : Tendsto (fun n => Real.sqrt (∫ z, ‖μn n z - μ' z‖ ^ 2)) atTop (𝓝 0) := by
    simpa using hD1.sqrt
  have h2 : Tendsto (fun n => Real.sqrt (∫ z, ‖(μn n z - μ' z) * ((beurlingL2 (hsolA μ' hAdm' hLp') :
      Lp ℂ 2 (volume : Measure ℂ)) : ℂ → ℂ) z‖ ^ 2)) atTop (𝓝 0) := by
    simpa using hD2.sqrt
  have hRHS : Tendsto (fun n => (1 - k)⁻¹ * (Real.sqrt (∫ z, ‖μn n z - μ' z‖ ^ 2)
      + Real.sqrt (∫ z, ‖(μn n z - μ' z) * ((beurlingL2 (hsolA μ' hAdm' hLp') :
          Lp ℂ 2 (volume : Measure ℂ)) : ℂ → ℂ) z‖ ^ 2))) atTop (𝓝 0) := by
    simpa using (h1.add h2).const_mul ((1 - k)⁻¹)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hRHS ?_ ?_
  · filter_upwards with n
    exact norm_nonneg _
  · filter_upwards with n
    exact hbound n

theorem forward_limit_pd {μ : ℂ → ℂ} {k M : ℝ} {μn : ℕ → ℂ → ℂ} {Fn : ℕ → ℂ ≃ₜ ℂ}
    (hk0 : 0 ≤ k) (hk1 : k < 1) (hM0 : 0 ≤ M)
    (hμnC : ∀ n, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (μn n))
    (hμnS : ∀ n, HasCompactSupport (μn n))
    (hμnB : ∀ n z, ‖μn n z‖ ≤ k)
    (hμnSp : ∀ n z, μn n z ≠ 0 → ‖z‖ ≤ M)
    (hμnT : ∀ᵐ z ∂(MeasureTheory.volume : MeasureTheory.Measure ℂ),
      Filter.Tendsto (fun n => μn n z) Filter.atTop (nhds (μ z)))
    (hμbd : ∀ᵐ z ∂(MeasureTheory.volume : MeasureTheory.Measure ℂ), ‖μ z‖ ≤ k)
    (hFC : ∀ n, ContDiff ℝ 1 (Fn n : ℂ → ℂ))
    (hFCS : ∀ n, ContDiff ℝ 1 ((Fn n).symm : ℂ → ℂ))
    (hFB : ∀ n z, Work.MRMT.dzbar (Fn n : ℂ → ℂ) z = μn n z * Work.MRMT.dz (Fn n : ℂ → ℂ) z)
    (hFD : ∀ n, ∃ C R : ℝ, ∀ z : ℂ, R ≤ ‖z‖ → ‖Fn n z - z‖ ≤ C / ‖z‖) :
    ∃ (φ : ℂ → ℂ) (D : ℂ → ℂ) (Cd Rd : ℝ),
      Continuous φ ∧
      TendstoLocallyUniformly (fun n => (Fn n : ℂ → ℂ)) φ Filter.atTop ∧
      (∀ z : ℂ, Rd ≤ ‖z‖ → ‖φ z - z‖ ≤ Cd / ‖z‖) ∧
      (∀ n : ℕ, ∀ z : ℂ, Rd ≤ ‖z‖ → ‖Fn n z - z‖ ≤ Cd / ‖z‖) ∧
      (∀ K : Set ℂ, IsCompact K →
        Filter.Tendsto (fun n => MeasureTheory.eLpNorm (fun z => Work.MRMT.dz (Fn n : ℂ → ℂ) z - D z) 2
          ((MeasureTheory.volume : MeasureTheory.Measure ℂ).restrict K)) Filter.atTop (nhds 0)) := by
  classical
  have hk1pos : 0 < 1 - k := by linarith
  let V : ℝ := (volume (Metric.closedBall (0 : ℂ) M)).toReal
  have hV0 : 0 ≤ V := ENNReal.toReal_nonneg
  let E : ℝ := k * Real.sqrt V / (1 - k)
  have hE0 : 0 ≤ E := by dsimp only [E]; positivity
  let Cd : ℝ := 2 * E * Real.sqrt V / Real.pi
  let Rd : ℝ := max (2 * M) 1
  have hRd1 : 1 ≤ Rd := le_max_right (2 * M) 1
  have hCd0 : 0 ≤ Cd := by dsimp only [Cd]; positivity
  -- the coefficients are admissible and square integrable
  have hAdmn : ∀ n, Admissible (μn n) := fun n =>
    ⟨(hμnC n).continuous.aestronglyMeasurable, ⟨k, hk1, ae_of_all _ (hμnB n)⟩,
      (hμnS n).isBounded.subset subset_closure⟩
  have hLpn : ∀ n, MemLp (μn n) 2 (volume : Measure ℂ) := fun n =>
    (hμnC n).continuous.memLp_of_hasCompactSupport (hμnS n)
  have hbn : ∀ n, ∀ᵐ z ∂(volume : Measure ℂ), ‖μn n z‖ ≤ k := fun n => ae_of_all _ (hμnB n)
  -- `∂̄(Fn n)` is `L²` with compact support
  have hmem : ∀ n, MemLp (fun z => dzbar (Fn n : ℂ → ℂ) z) 2 (volume : Measure ℂ) := fun n =>
    (fw_memLp_dzbar (hFC n) (hμnS n) (hμnB n) (hFB n)).1
  have hcs : ∀ n, HasCompactSupport (fun z => dzbar (Fn n : ℂ → ℂ) z) := fun n =>
    (fw_memLp_dzbar (hFC n) (hμnS n) (hμnB n) (hFB n)).2
  have hmem3 : ∀ n, MemLp (fun z => dzbar (Fn n : ℂ → ℂ) z) 3 (volume : Measure ℂ) := fun n =>
    (Weyl.continuous_dzbar_of_contDiff (hFC n) (by norm_num)).memLp_of_hasCompactSupport (hcs n)
  -- `∂̄(Fn n)` is the Ahlfors--Bers solution
  have heq : ∀ n, (fun z => dzbar (Fn n : ℂ → ℂ) z)
      =ᵐ[(volume : Measure ℂ)] ((hsolA (μn n) (hAdmn n) (hLpn n) :
        Lp ℂ 2 (volume : Measure ℂ)) : ℂ → ℂ) := by
    intro n
    refine fw_ae_eq_hsolA_of_ae_eq_mul_one_add hk1 (hAdmn n) (hLpn n) (hmem n) (hbn n) ?_
    filter_upwards [dz_sub_one_eq_beurlingL2_pd (hFC n) (hFD n) (hcs n) (hmem n)] with z hz
    rw [hFB n z]
    have hz' : dz (Fn n : ℂ → ℂ) z = 1 + ((beurlingL2 ((hmem n).toLp
        (fun z => dzbar (Fn n : ℂ → ℂ) z)) : Lp ℂ 2 (volume : Measure ℂ)) : ℂ → ℂ) z := by
      linear_combination hz
    rw [hz']
  have htoLp : ∀ n, (hmem n).toLp (fun z => dzbar (Fn n : ℂ → ℂ) z)
      = hsolA (μn n) (hAdmn n) (hLpn n) := by
    intro n
    rw [Lp.ext_iff]
    exact (MemLp.coeFn_toLp (hmem n)).trans (heq n)
  have hnorm : ∀ n, ‖hsolA (μn n) (hAdmn n) (hLpn n)‖ ≤ E := fun n =>
    fpd_hsolA_norm_le hk0 hk1 (hAdmn n) (hLpn n) (hbn n) (hμnSp n)
  -- the admissible representative of the limit coefficient
  obtain ⟨μ', hAdm', hLp', hμ'eq, hμ'supp, hμ'bd⟩ :=
    fw_admissible_of_tendsto_ae hk1 hμnC hμnSp hμnT hμbd
  have hconv' : ∀ᵐ z ∂(volume : Measure ℂ), Tendsto (fun n => μn n z) atTop (𝓝 (μ' z)) := by
    filter_upwards [hμnT, hμ'eq] with z hz heq'
    rwa [heq']
  have hsolconv : Tendsto (fun n => ‖hsolA (μn n) (hAdmn n) (hLpn n) - hsolA μ' hAdm' hLp'‖)
      atTop (𝓝 0) :=
    fpd_hsolA_tendsto hk0 hk1 hAdm' hLp' hAdmn hLpn hbn hμ'bd (fun n => hμnSp n) hμ'supp hconv'
  -- uniform decay
  have hFdec : ∀ n z, Rd ≤ ‖z‖ → ‖Fn n z - z‖ ≤ Cd / ‖z‖ := by
    intro n z hz
    have h1 : ∫ w, ‖dzbar (Fn n : ℂ → ℂ) w‖ ^ 2 ≤ E ^ 2 := by
      have h2 : ∫ w, ‖dzbar (Fn n : ℂ → ℂ) w‖ ^ 2
          = ‖hsolA (μn n) (hAdmn n) (hLpn n)‖ ^ 2 := by
        rw [← fpd_norm_sq_Lp (hsolA (μn n) (hAdmn n) (hLpn n)), ← htoLp n]
        apply integral_congr_ae
        filter_upwards [MemLp.coeFn_toLp (hmem n)] with w hw
        rw [hw]
      rw [h2]
      exact pow_le_pow_left₀ (norm_nonneg _) (hnorm n) 2
    have h3 := fw_decay_cauchyTransform_le (ω := fun w => dzbar (Fn n : ℂ → ℂ) w)
      (M := M) (E := E) hM0 hE0 (hmem n)
      (fun w hw => hμnSp n w (fun h0 => hw (by rw [hFB n w, h0, zero_mul]))) h1
    rw [fpd_sub_id_eq_cauchyTransform_dzbar (hFC n) (hcs n) (hFD n) z]
    exact h3 z hz
  -- uniform area bound for the images of unit balls
  let A : ℝ := (volume (Metric.closedBall (0 : ℂ) (Rd + 2 + Cd))).toReal
  have hA0 : 0 ≤ A := ENNReal.toReal_nonneg
  have hvol : ∀ n : ℕ, ∀ z₀ : ℂ,
      (volume (Fn n '' Metric.ball z₀ (1 : ℝ))).toReal ≤ A := fun n z₀ =>
    fw_volume_image_ball_le (F := Fn n) hRd1 hCd0 (fun z hz => hFdec n z hz) z₀
  -- the uniform modulus of continuity
  have hdil : ∀ (n : ℕ) (z : ℂ), ‖dzbar ((Fn n : ℂ ≃ₜ ℂ) : ℂ → ℂ) z‖
      ≤ k * ‖dz ((Fn n : ℂ ≃ₜ ℂ) : ℂ → ℂ) z‖ := fun n z => by
    rw [hFB n z, norm_mul]
    exact mul_le_mul_of_nonneg_right (hμnB n z) (norm_nonneg _)
  obtain ⟨ω, hω, hmod⟩ := fw_exists_uniform_modulus hk0 hk1 hA0
    (fun n => hFC n) (fun n => (Fn n).injective) hdil hvol
  -- `L²`-Cauchy on compacta
  have hc : ∀ K : Set ℂ, IsCompact K → ∀ ε : ℝ, 0 < ε →
      ∃ N : ℕ, ∀ n m : ℕ, N ≤ n → N ≤ m →
        IntegrableOn (fun z => ‖Fn n z - Fn m z‖ ^ 2) K (volume : Measure ℂ) ∧
        ∫ z in K, ‖Fn n z - Fn m z‖ ^ 2 < ε := by
    intro K hK ε hε
    obtain ⟨R₀, hR₀⟩ := hK.isBounded.exists_norm_le
    let R : ℝ := max R₀ 1 + 1
    have hRpos : 0 < R := by dsimp only [R]; positivity
    have hKR : K ⊆ Metric.ball (0 : ℂ) R := by
      intro z hz
      have h1 : ‖z‖ ≤ R₀ := hR₀ z hz
      rw [Metric.mem_ball, dist_zero_right]
      dsimp only [R]
      linarith [le_max_left R₀ 1]
    let Mp : ℝ := M + 1
    have hMppos : 0 < Mp := by dsimp only [Mp]; linarith
    let cK : ℝ := (8 * Real.sqrt (Mp * R)) ^ 2
    have hcKpos : 0 < cK := by
      dsimp only [cK]
      have h : 0 < Mp * R := mul_pos hMppos hRpos
      positivity
    have hδpos : 0 < Real.sqrt (ε / (4 * cK)) := Real.sqrt_pos.mpr (by positivity)
    have hev : ∀ᶠ n : ℕ in atTop,
        ‖hsolA (μn n) (hAdmn n) (hLpn n) - hsolA μ' hAdm' hLp'‖ < Real.sqrt (ε / (4 * cK)) := by
      have h := (Metric.tendsto_nhds.mp hsolconv) (Real.sqrt (ε / (4 * cK))) hδpos
      simpa [dist_eq_norm] using h
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp hev
    refine ⟨N, fun n m hn hm => ⟨?_, ?_⟩⟩
    · exact ContinuousOn.integrableOn_compact hK
        (((Fn n).continuous.sub (Fn m).continuous).norm.pow 2).continuousOn
    · have hpt : ∀ z, Fn n z - Fn m z
          = cauchyTransform (fun w => dzbar (Fn n : ℂ → ℂ) w - dzbar (Fn m : ℂ → ℂ) w) z := by
        intro z
        rw [fpd_cauchyTransform_sub (p := 3) (by norm_num) (hmem3 n) (hcs n) (hmem3 m) (hcs m) z,
          ← fpd_sub_id_eq_cauchyTransform_dzbar (hFC n) (hcs n) (hFD n) z,
          ← fpd_sub_id_eq_cauchyTransform_dzbar (hFC m) (hcs m) (hFD m) z]
        ring
      have hsupp : Function.support
          (fun z => dzbar (Fn n : ℂ → ℂ) z - dzbar (Fn m : ℂ → ℂ) z)
          ⊆ Metric.ball (0 : ℂ) Mp := by
        intro z hz
        rw [Function.mem_support] at hz
        rw [Metric.mem_ball, dist_zero_right]
        dsimp only [Mp]
        by_contra hcon
        rw [not_lt] at hcon
        have hMz : M < ‖z‖ := by linarith
        have h0n : dzbar (Fn n : ℂ → ℂ) z = 0 := by
          rw [hFB n z]
          have hμ0 : μn n z = 0 := by
            by_contra hne
            exact absurd (hμnSp n z hne) (not_le.mpr hMz)
          rw [hμ0, zero_mul]
        have h0m : dzbar (Fn m : ℂ → ℂ) z = 0 := by
          rw [hFB m z]
          have hμ0 : μn m z = 0 := by
            by_contra hne
            exact absurd (hμnSp m z hne) (not_le.mpr hMz)
          rw [hμ0, zero_mul]
        rw [h0n, h0m, sub_self] at hz
        exact hz rfl
      have h4 : ∫ z, ‖dzbar (Fn n : ℂ → ℂ) z - dzbar (Fn m : ℂ → ℂ) z‖ ^ 2
          = ‖hsolA (μn n) (hAdmn n) (hLpn n) - hsolA (μn m) (hAdmn m) (hLpn m)‖ ^ 2 := by
        rw [← fpd_norm_sq_Lp (hsolA (μn n) (hAdmn n) (hLpn n)
          - hsolA (μn m) (hAdmn m) (hLpn m)), ← htoLp n, ← htoLp m]
        apply integral_congr_ae
        filter_upwards [Lp.coeFn_sub ((hmem n).toLp (fun z => dzbar (Fn n : ℂ → ℂ) z))
            ((hmem m).toLp (fun z => dzbar (Fn m : ℂ → ℂ) z)),
          MemLp.coeFn_toLp (hmem n), MemLp.coeFn_toLp (hmem m)] with z h1 h2 h3
        rw [h1]
        simp only [Pi.sub_apply]
        rw [h2, h3]
      have h6 : ‖hsolA (μn n) (hAdmn n) (hLpn n) - hsolA (μn m) (hAdmn m) (hLpn m)‖
          < 2 * Real.sqrt (ε / (4 * cK)) := by
        have h9 : ‖hsolA (μn n) (hAdmn n) (hLpn n) - hsolA (μn m) (hAdmn m) (hLpn m)‖
            ≤ ‖hsolA (μn n) (hAdmn n) (hLpn n) - hsolA μ' hAdm' hLp'‖
              + ‖hsolA (μn m) (hAdmn m) (hLpn m) - hsolA μ' hAdm' hLp'‖ := by
          have h := norm_sub_le (hsolA (μn n) (hAdmn n) (hLpn n) - hsolA μ' hAdm' hLp')
            (hsolA (μn m) (hAdmn m) (hLpn m) - hsolA μ' hAdm' hLp')
          have heq'' : (hsolA (μn n) (hAdmn n) (hLpn n) - hsolA μ' hAdm' hLp')
              - (hsolA (μn m) (hAdmn m) (hLpn m) - hsolA μ' hAdm' hLp')
              = hsolA (μn n) (hAdmn n) (hLpn n) - hsolA (μn m) (hAdmn m) (hLpn m) := by
            abel
          rwa [heq''] at h
        linarith [h9, hN n hn, hN m hm]
      have h7 : ‖hsolA (μn n) (hAdmn n) (hLpn n) - hsolA (μn m) (hAdmn m) (hLpn m)‖ ^ 2
          < ε / cK := by
        have h8 : (2 * Real.sqrt (ε / (4 * cK))) ^ 2 = ε / cK := by
          rw [mul_pow, Real.sq_sqrt (by positivity), show (2 : ℝ) ^ 2 = 4 by norm_num]
          field_simp
        calc ‖hsolA (μn n) (hAdmn n) (hLpn n) - hsolA (μn m) (hAdmn m) (hLpn m)‖ ^ 2
            < (2 * Real.sqrt (ε / (4 * cK))) ^ 2 :=
              pow_lt_pow_left₀ h6 (norm_nonneg _) (by norm_num)
          _ = ε / cK := h8
      have hfun : (fun z => ‖Fn n z - Fn m z‖ ^ 2)
          = fun z => ‖cauchyTransform
              (fun w => dzbar (Fn n : ℂ → ℂ) w - dzbar (Fn m : ℂ → ℂ) w) z‖ ^ 2 :=
        funext fun z => by rw [hpt z]
      rw [hfun]
      have hintball : IntegrableOn
          (fun z => ‖cauchyTransform
            (fun w => dzbar (Fn n : ℂ → ℂ) w - dzbar (Fn m : ℂ → ℂ) w) z‖ ^ 2)
          (Metric.ball (0 : ℂ) R) (volume : Measure ℂ) := by
        have hcont : Continuous (fun z => cauchyTransform
            (fun w => dzbar (Fn n : ℂ → ℂ) w - dzbar (Fn m : ℂ → ℂ) w) z) := by
          rw [show (fun z => cauchyTransform
                (fun w => dzbar (Fn n : ℂ → ℂ) w - dzbar (Fn m : ℂ → ℂ) w) z)
              = fun z => Fn n z - Fn m z from funext fun z => (hpt z).symm]
          exact (Fn n).continuous.sub (Fn m).continuous
        exact (ContinuousOn.integrableOn_compact (isCompact_closedBall (0 : ℂ) R)
          ((hcont.norm.pow 2).continuousOn)).mono_set Metric.ball_subset_closedBall
      calc ∫ z in K, ‖cauchyTransform
              (fun w => dzbar (Fn n : ℂ → ℂ) w - dzbar (Fn m : ℂ → ℂ) w) z‖ ^ 2
          ≤ ∫ z in Metric.ball (0 : ℂ) R, ‖cauchyTransform
              (fun w => dzbar (Fn n : ℂ → ℂ) w - dzbar (Fn m : ℂ → ℂ) w) z‖ ^ 2 :=
            setIntegral_mono_set hintball (Eventually.of_forall fun z => sq_nonneg _)
              (Eventually.of_forall hKR)
        _ ≤ cK * ∫ z, ‖dzbar (Fn n : ℂ → ℂ) z - dzbar (Fn m : ℂ → ℂ) z‖ ^ 2 :=
            fw_integral_normSq_cauchyTransform_le hMppos hRpos ((hmem n).sub (hmem m)) hsupp
        _ = cK * ‖hsolA (μn n) (hAdmn n) (hLpn n) - hsolA (μn m) (hAdmn m) (hLpn m)‖ ^ 2 := by
            rw [h4]
        _ < cK * (ε / cK) := mul_lt_mul_of_pos_left h7 hcKpos
        _ = ε := by rw [mul_comm, div_mul_cancel₀ _ (ne_of_gt hcKpos)]
  obtain ⟨φ, hφc, hφconv⟩ := exists_tendstoLocallyUniformly_of_l2_of_modulus hω hmod hc
  have hφconv' := hφconv
  have hpt : ∀ z : ℂ, Tendsto (fun n => Fn n z) atTop (𝓝 (φ z)) := by
    intro z
    rw [Metric.tendsto_nhds]
    intro ε hε
    rw [Metric.tendstoLocallyUniformly_iff] at hφconv'
    obtain ⟨t, ht, hev⟩ := hφconv' ε hε z
    obtain ⟨δ, hδ, hδt⟩ := Metric.mem_nhds_iff.mp ht
    exact hev.mono fun n hn => by rw [dist_comm]; exact hn z (hδt (Metric.mem_ball_self hδ))
  refine ⟨φ, fun z => 1 + ((beurlingL2 (hsolA μ' hAdm' hLp') :
      Lp ℂ 2 (volume : Measure ℂ)) : ℂ → ℂ) z, Cd, Rd, hφc, hφconv, ?_, ?_, ?_⟩
  · intro z hz
    have h2 : Tendsto (fun n => ‖Fn n z - z‖) atTop (𝓝 (‖φ z - z‖)) :=
      (hpt z).sub tendsto_const_nhds |>.norm
    exact le_of_tendsto' h2 (fun n => hFdec n z hz)
  · intro n z hz
    exact hFdec n z hz
  · intro K hK
    have hLpconv : Tendsto (fun n => beurlingL2 (hsolA (μn n) (hAdmn n) (hLpn n))) atTop
        (𝓝 (beurlingL2 (hsolA μ' hAdm' hLp'))) := by
      rw [Metric.tendsto_nhds]
      intro ε hε
      have h := Metric.tendsto_nhds.mp hsolconv ε hε
      filter_upwards [h] with n hn
      rw [dist_zero_right] at hn
      rw [Real.norm_of_nonneg (norm_nonneg _)] at hn
      rw [dist_eq_norm, ← map_sub, norm_beurlingL2]
      exact hn
    have hEconv : Tendsto (fun n => eLpNorm (fun z =>
        (beurlingL2 (hsolA (μn n) (hAdmn n) (hLpn n)) : Lp ℂ 2 (volume : Measure ℂ)) z
        - (beurlingL2 (hsolA μ' hAdm' hLp') : Lp ℂ 2 (volume : Measure ℂ)) z) 2
        (volume : Measure ℂ)) atTop (𝓝 0) :=
      (MeasureTheory.Lp.tendsto_Lp_iff_tendsto_eLpNorm'
        (f := fun n => beurlingL2 (hsolA (μn n) (hAdmn n) (hLpn n)))
        (f_lim := beurlingL2 (hsolA μ' hAdm' hLp'))).mp hLpconv
    have hae : ∀ n, (fun z => dz (Fn n : ℂ → ℂ) z
          - (1 + ((beurlingL2 (hsolA μ' hAdm' hLp') :
              Lp ℂ 2 (volume : Measure ℂ)) : ℂ → ℂ) z))
        =ᵐ[(volume : Measure ℂ)] (fun z =>
            (beurlingL2 (hsolA (μn n) (hAdmn n) (hLpn n)) : Lp ℂ 2 (volume : Measure ℂ)) z
            - (beurlingL2 (hsolA μ' hAdm' hLp') : Lp ℂ 2 (volume : Measure ℂ)) z) := by
      intro n
      have hid := dz_sub_one_eq_beurlingL2_pd (hFC n) (hFD n) (hcs n) (hmem n)
      filter_upwards [hid] with z hz
      rw [← htoLp n]
      linear_combination hz
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hEconv ?_ ?_
    · filter_upwards with n
      exact bot_le
    · filter_upwards with n
      calc eLpNorm (fun z => dz (Fn n : ℂ → ℂ) z
              - (1 + ((beurlingL2 (hsolA μ' hAdm' hLp') :
                  Lp ℂ 2 (volume : Measure ℂ)) : ℂ → ℂ) z)) 2
            ((volume : Measure ℂ).restrict K)
          ≤ eLpNorm (fun z => dz (Fn n : ℂ → ℂ) z
              - (1 + ((beurlingL2 (hsolA μ' hAdm' hLp') :
                  Lp ℂ 2 (volume : Measure ℂ)) : ℂ → ℂ) z)) 2 (volume : Measure ℂ) :=
            eLpNorm_mono_measure _ Measure.restrict_le_self
        _ = eLpNorm (fun z => (beurlingL2 (hsolA (μn n) (hAdmn n) (hLpn n)) :
                Lp ℂ 2 (volume : Measure ℂ)) z
              - (beurlingL2 (hsolA μ' hAdm' hLp') : Lp ℂ 2 (volume : Measure ℂ)) z) 2
              (volume : Measure ℂ) :=
            eLpNorm_congr_ae (hae n)


end Work.MRMT.Found
