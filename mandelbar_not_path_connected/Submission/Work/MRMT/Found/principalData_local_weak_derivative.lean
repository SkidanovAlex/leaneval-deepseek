/-
Work.MRMT.Found — the local weak `∂`- and `∂̄`-derivatives of the principal solution.

`principalData_local_weak_derivative`: for an admissible coefficient `μ` and a `PrincipalData μ`,
the homeomorphism `φ` has a weak `∂`-derivative `D ∈ L²(B(0,R))` on every ball of radius `R`,
and the weak `∂̄`-derivative of `φ` is `μ D`.

The proof does **not** use the field `PrincipalData.dz_tendsto`.  What it uses is

* the uniform `L²` bound `∫_{B(0,R)} ‖∂(F n)‖² ≤ C` for the approximating `C¹` diffeomorphisms
  (`Work.MRMT.Found.uniform_dz_bound`);
* integration by parts for `C¹` functions (`∫ ∂(F n) · ψ = -∫ F n · ∂ψ`, and likewise for `∂̄`),
  together with the locally uniform convergence `F n → φ`, which shows that for a `C¹` test
  function `ψ` supported in `B(0,R)` the pairings `ψ ↦ -∫ φ · ∂ψ` and `ψ ↦ -∫ φ · ∂̄ψ` are the
  limits of the pairings against `F n` and are bounded by `√C ‖ψ‖_{L²}`;
* the Riesz representation theorem (via `LinearMap.extendOfNorm`), which produces
  `D ∈ L²(B(0,R))` with `∫ D ψ = -∫ φ ∂ψ` for every test function `ψ`
  (`Work.MRMT.Found.PLWD.exists_weak_dz_deriv_of_bound_memLp`);
* the weak convergence of `∂(F n)` towards `D` on the whole of `L²(B(0,R))`, obtained from the
  density of the test functions (`Work.MRMT.Found.PLWD.denseRange_testLp`);
* dominated convergence for the coefficients `μ n → μ`
  (`Work.MRMT.Found.PLWD.tendsto_integral_normSq_mu_sub_mul`).
-/
import Mathlib
import Submission.Work.MRMT.Found.Defs
import Submission.Work.MRMT.Found.PLWD.Defs
import Submission.Work.MRMT.Found.uniform_dz_bound
import Submission.Work.MRMT.Found.dzSq_integral_le_area
import Submission.Work.MRMT.Beltrami.integral_mul_dz_eq_neg
import Submission.Work.MRMT.QC.integral_mul_dzbar_eq_neg
import Submission.Work.MRMT.Found.differentiableOn_of_tendstoLocallyUniformly_of_lintegral_tendsto
import Submission.Work.MRMT.Found.PLWD.denseRange_testLp
import Submission.Work.MRMT.Found.PLWD.exists_weak_dz_deriv_of_bound_memLp
import Submission.Work.MRMT.Found.PLWD.tendsto_integral_normSq_mu_sub_mul

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


noncomputable section
open MeasureTheory Filter Topology Complex Function
open scoped Distributions Topology ENNReal
set_option maxHeartbeats 800000

namespace Work.MRMT.Found

/-! ## Elementary properties of `∂`, `∂̄` on test functions -/

/-! ## Helpers for the main theorem -/

theorem plwd_continuous_dz {f : ℂ → ℂ} (hf : ContDiff ℝ 1 f) : Continuous (dz f) := by
  have h : Continuous (fderiv ℝ f) := hf.continuous_fderiv (by norm_num)
  unfold dz
  simp only [div_eq_mul_inv]
  exact ((h.clm_apply continuous_const).sub
    (continuous_const.mul (h.clm_apply continuous_const))).mul_const _

theorem plwd_continuous_dzbar {f : ℂ → ℂ} (hf : ContDiff ℝ 1 f) : Continuous (dzbar f) := by
  have h : Continuous (fderiv ℝ f) := hf.continuous_fderiv (by norm_num)
  unfold dzbar
  simp only [div_eq_mul_inv]
  exact ((h.clm_apply continuous_const).add
    (continuous_const.mul (h.clm_apply continuous_const))).mul_const _

theorem plwd_dz_eq_zero_of_notMem_tsupport {f : ℂ → ℂ} {x : ℂ} (hx : x ∉ tsupport f) :
    dz f x = 0 := by
  have h0 : f =ᶠ[𝓝 x] 0 := by
    have : (tsupport f)ᶜ ∈ 𝓝 x := (isClosed_tsupport f).isOpen_compl.mem_nhds hx
    filter_upwards [this] with y hy
    exact image_eq_zero_of_notMem_tsupport hy
  have hf' : fderiv ℝ f x = fderiv ℝ (fun _ : ℂ => (0 : ℂ)) x := h0.fderiv_eq
  simp only [dz]
  rw [hf']
  simp

theorem plwd_dzbar_eq_zero_of_notMem_tsupport {f : ℂ → ℂ} {x : ℂ} (hx : x ∉ tsupport f) :
    dzbar f x = 0 := by
  have h0 : f =ᶠ[𝓝 x] 0 := by
    have : (tsupport f)ᶜ ∈ 𝓝 x := (isClosed_tsupport f).isOpen_compl.mem_nhds hx
    filter_upwards [this] with y hy
    exact image_eq_zero_of_notMem_tsupport hy
  have hf' : fderiv ℝ f x = fderiv ℝ (fun _ : ℂ => (0 : ℂ)) x := h0.fderiv_eq
  simp only [dzbar]
  rw [hf']
  simp

theorem plwd_support_dz_subset_closedBall {R : ℝ} (ψ : testSpace R) :
    Function.support (dz (ψ : ℂ → ℂ)) ⊆ Metric.closedBall 0 R := by
  intro x hx
  by_contra hxK
  have hxt : x ∉ tsupport (ψ : ℂ → ℂ) := fun h =>
    hxK (subset_trans ψ.2.2.2 Metric.ball_subset_closedBall h)
  exact hx (plwd_dz_eq_zero_of_notMem_tsupport hxt)

theorem plwd_support_dzbar_subset_closedBall {R : ℝ} (ψ : testSpace R) :
    Function.support (dzbar (ψ : ℂ → ℂ)) ⊆ Metric.closedBall 0 R := by
  intro x hx
  by_contra hxK
  have hxt : x ∉ tsupport (ψ : ℂ → ℂ) := fun h =>
    hxK (subset_trans ψ.2.2.2 Metric.ball_subset_closedBall h)
  exact hx (plwd_dzbar_eq_zero_of_notMem_tsupport hxt)

theorem plwd_hasCompactSupport_dz {R : ℝ} (ψ : testSpace R) :
    HasCompactSupport (dz (ψ : ℂ → ℂ)) :=
  HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall 0 R)
    (plwd_support_dz_subset_closedBall ψ)

theorem plwd_hasCompactSupport_dzbar {R : ℝ} (ψ : testSpace R) :
    HasCompactSupport (dzbar (ψ : ℂ → ℂ)) :=
  HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall 0 R)
    (plwd_support_dzbar_subset_closedBall ψ)

theorem plwd_integrable_of_bounded_compact {g : ℂ → ℂ} {K : Set ℂ} (hK : IsCompact K)
    (hsupp : Function.support g ⊆ K)
    (hmeas : AEStronglyMeasurable g (volume : Measure ℂ)) {C : ℝ}
    (hb : ∀ᵐ z ∂(volume : Measure ℂ), z ∈ K → ‖g z‖ ≤ C) : Integrable g (volume : Measure ℂ) := by
  have hg : Integrable (K.indicator (fun _ : ℂ => C)) (volume : Measure ℂ) := by
    rw [integrable_indicator_iff hK.measurableSet]
    exact integrableOn_const (hK.measure_lt_top.ne)
  refine hg.mono' hmeas ?_
  filter_upwards [hb] with z hz
  by_cases hzK : z ∈ K
  · rw [Set.indicator_of_mem hzK]
    exact hz hzK
  · have hgz : g z = 0 := by
      by_contra h
      exact hzK (hsupp (Function.mem_support.mpr h))
    rw [hgz, Set.indicator_of_notMem hzK, norm_zero]

theorem plwd_norm_toLp_sq {α : Type*} [MeasurableSpace α] {μ' : Measure α} {f : α → ℂ}
    (hf : MemLp f 2 μ') : ‖hf.toLp f‖ ^ 2 = ∫ x, ‖f x‖ ^ 2 ∂μ' := by
  have h1 : inner ℝ (hf.toLp f : Lp ℂ 2 μ') (hf.toLp f : Lp ℂ 2 μ') = ∫ x, ‖f x‖ ^ 2 ∂μ' := by
    rw [L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [hf.coeFn_toLp] with x hx
    rw [hx, real_inner_self_eq_norm_sq]
  rw [← h1, real_inner_self_eq_norm_sq]

theorem plwd_norm_testLp (R : ℝ) (ψ : testSpace R) : ‖testLp R ψ‖ ^ 2
    = ∫ z, ‖(ψ : ℂ → ℂ) z‖ ^ 2 ∂((volume : Measure ℂ).restrict (Metric.ball 0 R)) :=
  plwd_norm_toLp_sq (memLp_of_mem_testSpace ψ.2)

theorem plwd_norm_integral_mul_le {f g : ℂ → ℂ} {μ' : Measure ℂ}
    (hf : MemLp f 2 μ') (hg : MemLp g 2 μ') :
    ‖∫ z, f z * g z ∂μ'‖ ≤
      Real.sqrt (∫ z, ‖f z‖ ^ 2 ∂μ') * Real.sqrt (∫ z, ‖g z‖ ^ 2 ∂μ') := by
  have h2 : (2 : ℝ).HolderConjugate 2 := by rw [Real.holderConjugate_iff]; norm_num
  have hf' : MemLp f (ENNReal.ofReal (2 : ℝ)) μ' := by simpa using hf
  have hg' : MemLp g (ENNReal.ofReal (2 : ℝ)) μ' := by simpa using hg
  have hle := integral_mul_norm_le_Lp_mul_Lq (μ := μ') h2 hf' hg'
  calc ‖∫ z, f z * g z ∂μ'‖ ≤ ∫ z, ‖f z * g z‖ ∂μ' := norm_integral_le_integral_norm _
    _ = ∫ z, ‖f z‖ * ‖g z‖ ∂μ' := by simp only [norm_mul]
    _ ≤ (∫ z, ‖f z‖ ^ 2 ∂μ') ^ (1 / 2) * (∫ z, ‖g z‖ ^ 2 ∂μ') ^ (1 / 2) := hle
    _ = Real.sqrt (∫ z, ‖f z‖ ^ 2 ∂μ') * Real.sqrt (∫ z, ‖g z‖ ^ 2 ∂μ') := by
        simp only [Real.sqrt_eq_rpow, Real.rpow_two]

theorem plwd_integrable_mul_of_memLp {f g : ℂ → ℂ} {μ' : Measure ℂ}
    (hf : MemLp f 2 μ') (hg : MemLp g 2 μ') :
    Integrable (fun z => f z * g z) μ' := by
  have hfs : Integrable (fun z => ‖f z‖ ^ 2) μ' := by
    simpa using hf.integrable_norm_rpow (p := 2) (by norm_num) (by norm_num)
  have hgs : Integrable (fun z => ‖g z‖ ^ 2) μ' := by
    simpa using hg.integrable_norm_rpow (p := 2) (by norm_num) (by norm_num)
  refine (Integrable.mono' ((hfs.add hgs).const_mul (1/2))
    (hf.aestronglyMeasurable.mul hg.aestronglyMeasurable) ?_)
  filter_upwards with z
  rw [norm_mul]
  have h : (‖f z‖ - ‖g z‖) ^ 2 ≥ 0 := sq_nonneg _
  have h2 : ‖f z‖ * ‖g z‖ ≤ 1 / 2 * (‖f z‖ ^ 2 + ‖g z‖ ^ 2) := by nlinarith
  exact h2

/-- Real-valued version of the previous statement. -/
theorem plwd_integral_ball_eq_real {R : ℝ} {f : ℂ → ℝ} (h : ∀ z ∉ Metric.ball 0 R, f z = 0) :
    ∫ z, f z = ∫ z, f z ∂((volume : Measure ℂ).restrict (Metric.ball 0 R)) :=
  (setIntegral_eq_integral_of_forall_compl_eq_zero h).symm

/-- The integral over the plane of a function supported in the ball equals its integral for the
restricted measure on the ball. -/
theorem plwd_integral_ball_eq {R : ℝ} {f : ℂ → ℂ} (h : ∀ z ∉ Metric.ball 0 R, f z = 0) :
    ∫ z, f z = ∫ z, f z ∂((volume : Measure ℂ).restrict (Metric.ball 0 R)) :=
  (setIntegral_eq_integral_of_forall_compl_eq_zero h).symm

theorem plwd_support_mul_subset {R : ℝ} {ψ : ℂ → ℂ} (hψ : tsupport ψ ⊆ Metric.ball 0 R)
    (g : ℂ → ℂ) : ∀ z ∉ Metric.ball 0 R, g z * ψ z = 0 := by
  intro z hz
  have hz0 : ψ z = 0 := by
    by_contra h
    exact hz (hψ (subset_tsupport _ (Function.mem_support.mpr h)))
  rw [hz0, mul_zero]

/-- `∂(F n)` is square integrable on the ball. -/
theorem plwd_memLp_dz {μ : ℂ → ℂ} (d : PrincipalData μ) (R : ℝ) (hR : 0 < R) (n : ℕ) :
    MemLp (dz ((d.Fn n : ℂ ≃ₜ ℂ) : ℂ → ℂ)) 2
      ((volume : Measure ℂ).restrict (Metric.ball 0 R)) := by
  haveI hfin : IsFiniteMeasure ((volume : Measure ℂ).restrict (Metric.ball 0 R)) := by
    rw [isFiniteMeasure_restrict]
    exact (measure_ball_lt_top (x := (0 : ℂ)) (r := R)).ne
  have hc : Continuous (dz ((d.Fn n : ℂ ≃ₜ ℂ) : ℂ → ℂ)) := plwd_continuous_dz (d.contDiff_Fn n)
  obtain ⟨M, hM⟩ := (isCompact_closedBall (0 : ℂ) R).exists_bound_of_continuousOn hc.continuousOn
  refine MemLp.of_bound hc.aestronglyMeasurable M ?_
  rw [MeasureTheory.ae_restrict_iff' Metric.isOpen_ball.measurableSet]
  filter_upwards with z hz
  exact hM z (Metric.ball_subset_closedBall hz)

/-- `μ · ψ` is square integrable on the ball for an admissible `μ`. -/
theorem plwd_memLp_mu_mul {μ : ℂ → ℂ} (hμ : Admissible μ) {R : ℝ} {ψ : ℂ → ℂ}
    (hψm : MemLp ψ 2 ((volume : Measure ℂ).restrict (Metric.ball 0 R))) :
    MemLp (fun z => μ z * ψ z) 2 ((volume : Measure ℂ).restrict (Metric.ball 0 R)) := by
  obtain ⟨k, hk, hkb⟩ := hμ.bound
  have hbν : ∀ᵐ z ∂((volume : Measure ℂ).restrict (Metric.ball 0 R)), ‖μ z‖ ≤ max k 1 := by
    rw [MeasureTheory.ae_restrict_iff' Metric.isOpen_ball.measurableSet]
    filter_upwards [hkb] with z hz _
    exact le_trans hz (le_max_left _ _)
  have hg : MemLp (fun z => max k 1 * ‖ψ z‖) 2
      ((volume : Measure ℂ).restrict (Metric.ball 0 R)) := by
    simpa using hψm.norm.const_mul (max k 1)
  refine MemLp.of_le (g := fun z => max k 1 * ‖ψ z‖) hg
    ((hμ.meas.mono_measure Measure.restrict_le_self).mul hψm.aestronglyMeasurable) ?_
  filter_upwards [hbν] with z hz
  rw [norm_mul, Real.norm_of_nonneg
    (mul_nonneg (le_trans zero_le_one (le_max_right k 1)) (norm_nonneg _))]
  exact mul_le_mul_of_nonneg_right hz (norm_nonneg _)

/-- `(μ n - μ) · ψ` is square integrable on the ball. -/
theorem plwd_memLp_mu_sub_mul {μ : ℂ → ℂ} (hμ : Admissible μ) (d : PrincipalData μ) {R : ℝ}
    {ψ : ℂ → ℂ} (hψm : MemLp ψ 2 ((volume : Measure ℂ).restrict (Metric.ball 0 R))) (n : ℕ) :
    MemLp (fun z => (d.μn n z - μ z) * ψ z) 2
      ((volume : Measure ℂ).restrict (Metric.ball 0 R)) := by
  obtain ⟨k, hk, hkb⟩ := hμ.bound
  have hk0 : 0 ≤ d.k := le_trans (norm_nonneg (d.μn n 0)) (d.norm_μn n 0)
  have hbν : ∀ᵐ z ∂((volume : Measure ℂ).restrict (Metric.ball 0 R)),
      ‖d.μn n z - μ z‖ ≤ d.k + max k 1 := by
    rw [MeasureTheory.ae_restrict_iff' Metric.isOpen_ball.measurableSet]
    filter_upwards [hkb] with z hz _
    calc ‖d.μn n z - μ z‖ ≤ ‖d.μn n z‖ + ‖μ z‖ := norm_sub_le _ _
      _ ≤ d.k + max k 1 := add_le_add (d.norm_μn n z) (le_trans hz (le_max_left _ _))
  have hg : MemLp (fun z => (d.k + max k 1) * ‖ψ z‖) 2
      ((volume : Measure ℂ).restrict (Metric.ball 0 R)) := by
    simpa using hψm.norm.const_mul (d.k + max k 1)
  refine MemLp.of_le (g := fun z => (d.k + max k 1) * ‖ψ z‖)
    hg ?_ ?_
  · exact (((d.contDiff_μn n).continuous.aestronglyMeasurable.sub
      (hμ.meas.mono_measure Measure.restrict_le_self)).mul hψm.aestronglyMeasurable)
  · filter_upwards [hbν] with z hz
    rw [norm_mul, Real.norm_of_nonneg
      (mul_nonneg (by linarith [hk0, le_trans zero_le_one (le_max_right k 1)]) (norm_nonneg _))]
    exact mul_le_mul_of_nonneg_right hz (norm_nonneg _)

/-- Convergence of `∫ F n · η` against a compactly supported continuous `η` supported in the
closed ball. -/
theorem plwd_tendsto_integral_Fn_mul {μ : ℂ → ℂ} (d : PrincipalData μ) {R : ℝ} {η : ℂ → ℂ}
    (hηc : Continuous η) (hηcs : HasCompactSupport η)
    (hηsupp : Function.support η ⊆ Metric.closedBall 0 R) :
    Filter.Tendsto (fun n => ∫ z, (d.Fn n : ℂ → ℂ) z * η z) Filter.atTop
      (nhds (∫ z, (d.φ : ℂ → ℂ) z * η z)) := by
  have hunif := (tendstoLocallyUniformly_iff_forall_isCompact.mp d.tendsto_Fn)
    (Metric.closedBall 0 R) (isCompact_closedBall 0 R)
  have hlim0 := tendsto_integral_sub_mul_of_tendstoUniformlyOn_aux (K := Metric.closedBall 0 R)
    (isCompact_closedBall 0 R) hunif hηsupp hηc.continuousOn
  have hintF : ∀ n, Integrable (fun z => (d.Fn n : ℂ → ℂ) z * η z) := fun n =>
    (((d.Fn n).continuous).mul hηc).integrable_of_hasCompactSupport hηcs.mul_left
  have hintφ : Integrable (fun z => (d.φ : ℂ → ℂ) z * η z) :=
    (d.φ.continuous.mul hηc).integrable_of_hasCompactSupport hηcs.mul_left
  have hEq : (fun n => ∫ z, ((d.Fn n : ℂ → ℂ) z - (d.φ : ℂ → ℂ) z) * η z)
      = fun n => (∫ z, (d.Fn n : ℂ → ℂ) z * η z) - (∫ z, (d.φ : ℂ → ℂ) z * η z) := by
    funext n
    rw [← integral_sub (hintF n) hintφ]
    exact integral_congr_ae (Filter.Eventually.of_forall fun z => by ring)
  rw [hEq] at hlim0
  exact tendsto_sub_nhds_zero_iff.mp hlim0

theorem plwd_exists_test_approx {R : ℝ} (hdense : DenseRange (testLp R)) {χ : ℂ → ℂ}
    (hχ : MemLp χ 2 ((volume : Measure ℂ).restrict (Metric.ball 0 R)))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ ψ : testSpace R,
      ∫ z, ‖(χ - (ψ : ℂ → ℂ)) z‖ ^ 2 ∂((volume : Measure ℂ).restrict (Metric.ball 0 R)) < ε := by
  have hcls : (hχ.toLp χ) ∈ closure (Set.range (testLp R)) := hdense (hχ.toLp χ)
  obtain ⟨y, hy, hydist⟩ := Metric.mem_closure_iff.mp hcls (Real.sqrt ε) (Real.sqrt_pos.mpr hε)
  obtain ⟨ψ, rfl⟩ := hy
  refine ⟨ψ, ?_⟩
  have hmem : MemLp (χ - (ψ : ℂ → ℂ)) 2 ((volume : Measure ℂ).restrict (Metric.ball 0 R)) :=
    hχ.sub (memLp_of_mem_testSpace ψ.2)
  have hkey : ∫ z, ‖(χ - (ψ : ℂ → ℂ)) z‖ ^ 2 ∂((volume : Measure ℂ).restrict (Metric.ball 0 R))
      = ‖hχ.toLp χ - testLp R ψ‖ ^ 2 := by
    rw [← plwd_norm_toLp_sq (μ' := (volume : Measure ℂ).restrict (Metric.ball 0 R)) hmem,
      MemLp.toLp_sub hχ (memLp_of_mem_testSpace ψ.2)]
    simp only [testLp_apply]
  rw [hkey]
  have h1 : ‖hχ.toLp χ - testLp R ψ‖ < Real.sqrt ε := by
    rw [← dist_eq_norm]
    exact hydist
  have h2 : ‖hχ.toLp χ - testLp R ψ‖ ^ 2 < ε := by
    have hs := Real.sq_sqrt hε.le
    nlinarith [h1, norm_nonneg (hχ.toLp χ - testLp R ψ), Real.sqrt_nonneg ε]
  exact h2

theorem plwd_tendsto_integral_mul_of_testSpace {R : ℝ} (hdense : DenseRange (testLp R))
    {v : ℕ → ℂ → ℂ} {w : ℂ → ℂ} {C : ℝ}
    (hv : ∀ n, MemLp (v n) 2 ((volume : Measure ℂ).restrict (Metric.ball 0 R)))
    (hw : MemLp w 2 ((volume : Measure ℂ).restrict (Metric.ball 0 R)))
    (hvC : ∀ n, ∫ z, ‖v n z‖ ^ 2 ∂((volume : Measure ℂ).restrict (Metric.ball 0 R)) ≤ C)
    (h : ∀ ψ : testSpace R,
      Filter.Tendsto (fun n => ∫ z, v n z * (ψ : ℂ → ℂ) z
          ∂((volume : Measure ℂ).restrict (Metric.ball 0 R)))
        Filter.atTop (nhds (∫ z, w z * (ψ : ℂ → ℂ) z
          ∂((volume : Measure ℂ).restrict (Metric.ball 0 R)))))
    {χ : ℂ → ℂ} (hχ : MemLp χ 2 ((volume : Measure ℂ).restrict (Metric.ball 0 R))) :
    Filter.Tendsto (fun n => ∫ z, v n z * χ z ∂((volume : Measure ℂ).restrict (Metric.ball 0 R)))
      Filter.atTop (nhds (∫ z, w z * χ z ∂((volume : Measure ℂ).restrict (Metric.ball 0 R)))) := by
  set ν : Measure ℂ := (volume : Measure ℂ).restrict (Metric.ball 0 R) with hν
  rw [Metric.tendsto_atTop]
  intro ε hε
  set B : ℝ := Real.sqrt (max C 0) + Real.sqrt (∫ z, ‖w z‖ ^ 2 ∂ν) with hB
  have hBnn : 0 ≤ B := by rw [hB]; positivity
  set δ : ℝ := ε / (2 * (B + 1)) with hδ
  have hδpos : 0 < δ := by rw [hδ]; positivity
  obtain ⟨ψ₀, hψ₀⟩ := plwd_exists_test_approx (R := R) hdense hχ (show (0:ℝ) < δ ^ 2 by positivity)
  set A : ℝ := ∫ z, ‖(χ - (ψ₀ : ℂ → ℂ)) z‖ ^ 2 ∂ν with hA
  have hAnn : 0 ≤ A := integral_nonneg (fun z => sq_nonneg _)
  have hδbound : B * Real.sqrt A < ε / 2 := by
    have hsqrtA : Real.sqrt A < δ := by
      rw [Real.sqrt_lt' hδpos]
      exact hψ₀
    have h2 : B * δ ≤ ε / 2 := by
      have hB1 : 0 < B + 1 := by linarith
      have hratio : B / (B + 1) ≤ 1 := (div_le_one hB1).mpr (by linarith)
      calc B * δ = (B / (B + 1)) * (ε / 2) := by
            rw [hδ]; field_simp
        _ ≤ 1 * (ε / 2) := mul_le_mul_of_nonneg_right hratio (by linarith)
        _ = ε / 2 := one_mul _
    rcases lt_or_eq_of_le hBnn with hBpos | hBeq
    · have h1 : B * Real.sqrt A < B * δ := mul_lt_mul_of_pos_left hsqrtA hBpos
      linarith
    · rw [← hBeq, zero_mul]
      linarith
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp (h ψ₀) (ε/2) (by linarith)
  refine ⟨N, fun n hn => ?_⟩
  have hmn : ‖(∫ z, v n z * (ψ₀ : ℂ → ℂ) z ∂ν) - (∫ z, w z * (ψ₀ : ℂ → ℂ) z ∂ν)‖ < ε / 2 := by
    simpa only [dist_eq_norm] using hN n hn
  have hInt1 : Integrable (fun z => v n z * χ z) ν := plwd_integrable_mul_of_memLp (hv n) hχ
  have hInt2 : Integrable (fun z => v n z * (ψ₀ : ℂ → ℂ) z) ν :=
    plwd_integrable_mul_of_memLp (hv n) (memLp_of_mem_testSpace ψ₀.2)
  have hInt3 : Integrable (fun z => w z * χ z) ν := plwd_integrable_mul_of_memLp hw hχ
  have hInt4 : Integrable (fun z => w z * (ψ₀ : ℂ → ℂ) z) ν :=
    plwd_integrable_mul_of_memLp hw (memLp_of_mem_testSpace ψ₀.2)
  have hEq1 : (∫ z, v n z * χ z ∂ν) - (∫ z, v n z * (ψ₀ : ℂ → ℂ) z ∂ν)
      = ∫ z, v n z * (χ - (ψ₀ : ℂ → ℂ)) z ∂ν := by
    rw [← integral_sub hInt1 hInt2]
    exact integral_congr_ae (Filter.Eventually.of_forall fun z => by
      simp only [Pi.sub_apply]; ring)
  have hEq2 : (∫ z, w z * (ψ₀ : ℂ → ℂ) z ∂ν) - (∫ z, w z * χ z ∂ν)
      = ∫ z, w z * ((ψ₀ : ℂ → ℂ) - χ) z ∂ν := by
    rw [← integral_sub hInt4 hInt3]
    exact integral_congr_ae (Filter.Eventually.of_forall fun z => by
      simp only [Pi.sub_apply]; ring)
  have hb1 : ‖∫ z, v n z * (χ - (ψ₀ : ℂ → ℂ)) z ∂ν‖ ≤ Real.sqrt (max C 0) * Real.sqrt A := by
    have hle := plwd_norm_integral_mul_le (hv n) (hχ.sub (memLp_of_mem_testSpace ψ₀.2))
    refine hle.trans ?_
    have hmax : ∫ z, ‖v n z‖ ^ 2 ∂ν ≤ max C 0 := le_trans (hvC n) (le_max_left _ _)
    have hs : Real.sqrt (∫ z, ‖v n z‖ ^ 2 ∂ν) ≤ Real.sqrt (max C 0) := Real.sqrt_le_sqrt hmax
    rw [show (∫ z, ‖(χ - (ψ₀ : ℂ → ℂ)) z‖ ^ 2 ∂ν) = A from hA.symm]
    exact mul_le_mul_of_nonneg_right hs (Real.sqrt_nonneg _)
  have hb2 : ‖∫ z, w z * ((ψ₀ : ℂ → ℂ) - χ) z ∂ν‖
      ≤ Real.sqrt (∫ z, ‖w z‖ ^ 2 ∂ν) * Real.sqrt A := by
    have hle := plwd_norm_integral_mul_le hw ((memLp_of_mem_testSpace ψ₀.2).sub hχ)
    have hEqA : ∫ z, ‖((ψ₀ : ℂ → ℂ) - χ) z‖ ^ 2 ∂ν = A := by
      rw [hA]
      refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
      simp only [Pi.sub_apply]
      rw [norm_sub_rev]
    calc ‖∫ z, w z * ((ψ₀ : ℂ → ℂ) - χ) z ∂ν‖
        ≤ Real.sqrt (∫ z, ‖w z‖ ^ 2 ∂ν)
            * Real.sqrt (∫ z, ‖((ψ₀ : ℂ → ℂ) - χ) z‖ ^ 2 ∂ν) := hle
      _ = Real.sqrt (∫ z, ‖w z‖ ^ 2 ∂ν) * Real.sqrt A := by rw [hEqA]
  have hsplit : (∫ z, v n z * χ z ∂ν) - (∫ z, w z * χ z ∂ν)
      = ((∫ z, v n z * χ z ∂ν) - (∫ z, v n z * (ψ₀ : ℂ → ℂ) z ∂ν))
        + ((∫ z, v n z * (ψ₀ : ℂ → ℂ) z ∂ν) - (∫ z, w z * (ψ₀ : ℂ → ℂ) z ∂ν))
        + ((∫ z, w z * (ψ₀ : ℂ → ℂ) z ∂ν) - (∫ z, w z * χ z ∂ν)) := by ring
  have hfin : ‖(∫ z, v n z * χ z ∂ν) - (∫ z, w z * χ z ∂ν)‖ ≤ B * Real.sqrt A + ε / 2 := by
    rw [hsplit, hEq1, hEq2]
    have htri : ‖(∫ z, v n z * (χ - (ψ₀ : ℂ → ℂ)) z ∂ν)
          + ((∫ z, v n z * (ψ₀ : ℂ → ℂ) z ∂ν) - (∫ z, w z * (ψ₀ : ℂ → ℂ) z ∂ν))
          + ∫ z, w z * ((ψ₀ : ℂ → ℂ) - χ) z ∂ν‖
        ≤ Real.sqrt (max C 0) * Real.sqrt A + ε / 2
          + Real.sqrt (∫ z, ‖w z‖ ^ 2 ∂ν) * Real.sqrt A := by
      refine le_trans (norm_add_le _ _) ?_
      have h3 : ‖∫ z, v n z * (χ - (ψ₀ : ℂ → ℂ)) z ∂ν
            + ((∫ z, v n z * (ψ₀ : ℂ → ℂ) z ∂ν) - (∫ z, w z * (ψ₀ : ℂ → ℂ) z ∂ν))‖
          ≤ Real.sqrt (max C 0) * Real.sqrt A + ε / 2 := by
        exact le_trans (norm_add_le _ _) (add_le_add hb1 hmn.le)
      exact add_le_add h3 hb2
    have hsum : Real.sqrt (max C 0) * Real.sqrt A
          + (Real.sqrt (∫ z, ‖w z‖ ^ 2 ∂ν) * Real.sqrt A) = B * Real.sqrt A := by
      rw [hB]; ring
    linarith [htri, hsum.le, hsum.ge]
  rw [dist_eq_norm]
  linarith [hfin, hδbound]


/-! ## The second weak-derivative identity -/

theorem plwd_second_identity {μ : ℂ → ℂ} (hμ : Admissible μ) (d : PrincipalData μ) {R : ℝ}
    (hR : 0 < R) {D : ℂ → ℂ}
    (hDm : MemLp D 2 ((volume : Measure ℂ).restrict (Metric.ball 0 R)))
    (hD : ∀ ψ : testSpace R, ∫ z, D z * (ψ : ℂ → ℂ) z = -∫ z, (d.φ : ℂ → ℂ) z * dz (ψ : ℂ → ℂ) z) :
    ∀ ψ : ℂ → ℂ, ContDiff ℝ 1 ψ → HasCompactSupport ψ → tsupport ψ ⊆ Metric.ball 0 R →
      ∫ z, μ z * D z * ψ z = -∫ z, (d.φ : ℂ → ℂ) z * dzbar ψ z := by
  intro ψ hψcd hψcs hψsub
  obtain ⟨C₀, hC₀⟩ := uniform_dz_bound hμ d R hR
  set ν : Measure ℂ := (volume : Measure ℂ).restrict (Metric.ball 0 R) with hν
  have hψm : MemLp (ψ : ℂ → ℂ) 2 ν := memLp_of_mem_testSpace ⟨hψcd, hψcs, hψsub⟩
  -- first convergence
  have h1 : Filter.Tendsto (fun n => ∫ z, d.μn n z * dz (d.Fn n : ℂ → ℂ) z * ψ z) Filter.atTop
      (nhds (-∫ z, (d.φ : ℂ → ℂ) z * dzbar ψ z)) := by
    have heq : ∀ n, ∫ z, d.μn n z * dz (d.Fn n : ℂ → ℂ) z * ψ z
        = ∫ z, dzbar (d.Fn n : ℂ → ℂ) z * ψ z := by
      intro n
      refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
      show d.μn n z * dz (d.Fn n : ℂ → ℂ) z * ψ z = dzbar (d.Fn n : ℂ → ℂ) z * ψ z
      rw [← d.beltrami_Fn n z]
    have h2 : Filter.Tendsto (fun n => ∫ z, dzbar (d.Fn n : ℂ → ℂ) z * ψ z) Filter.atTop
        (nhds (-∫ z, (d.φ : ℂ → ℂ) z * dzbar ψ z)) := by
      have hconv := plwd_tendsto_integral_Fn_mul d (plwd_continuous_dzbar hψcd)
        (plwd_hasCompactSupport_dzbar ⟨ψ, hψcd, hψcs, hψsub⟩)
        (plwd_support_dzbar_subset_closedBall ⟨ψ, hψcd, hψcs, hψsub⟩)
      have hibp : ∀ n, ∫ z, (d.Fn n : ℂ → ℂ) z * dzbar ψ z
          = -∫ z, dzbar (d.Fn n : ℂ → ℂ) z * ψ z := fun n =>
        Work.MRMT.QC.integral_mul_dzbar_eq_neg (d.contDiff_Fn n) hψcd hψcs
      have hconv2 : Filter.Tendsto (fun n => -∫ z, dzbar (d.Fn n : ℂ → ℂ) z * ψ z) Filter.atTop
          (nhds (∫ z, (d.φ : ℂ → ℂ) z * dzbar ψ z)) :=
        hconv.congr' (Filter.Eventually.of_forall hibp)
      simpa using hconv2.neg
    exact h2.congr' (Filter.Eventually.of_forall fun n => (heq n).symm)
  -- second convergence
  have h2 : Filter.Tendsto (fun n => ∫ z, d.μn n z * dz (d.Fn n : ℂ → ℂ) z * ψ z) Filter.atTop
      (nhds (∫ z, μ z * D z * ψ z)) := by
    have hsingle : ∀ n, ∫ z, d.μn n z * dz (d.Fn n : ℂ → ℂ) z * ψ z
        = (∫ z, dz (d.Fn n : ℂ → ℂ) z * ((d.μn n z - μ z) * ψ z) ∂ν)
          + (∫ z, dz (d.Fn n : ℂ → ℂ) z * (μ z * ψ z) ∂ν) := by
      intro n
      rw [plwd_integral_ball_eq (f := fun z => d.μn n z * dz ((d.Fn n : ℂ ≃ₜ ℂ) : ℂ → ℂ) z * ψ z)
        (plwd_support_mul_subset hψsub (fun z => d.μn n z * dz ((d.Fn n : ℂ ≃ₜ ℂ) : ℂ → ℂ) z))]
      rw [← integral_add
        (plwd_integrable_mul_of_memLp (plwd_memLp_dz d R hR n) (plwd_memLp_mu_sub_mul hμ d hψm n))
        (plwd_integrable_mul_of_memLp (plwd_memLp_dz d R hR n) (plwd_memLp_mu_mul hμ hψm))]
      refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
      simp only [Pi.add_apply]
      ring
    have hz1 : Filter.Tendsto (fun n => ∫ z, dz (d.Fn n : ℂ → ℂ) z * ((d.μn n z - μ z) * ψ z) ∂ν)
        Filter.atTop (nhds 0) := by
      rw [tendsto_zero_iff_norm_tendsto_zero]
      have hb : Filter.Tendsto (fun n => ∫ z, ‖(d.μn n z - μ z) * ψ z‖ ^ 2 ∂ν)
          Filter.atTop (nhds 0) := by
        have h := Work.MRMT.Found.PLWD.tendsto_integral_normSq_mu_sub_mul hμ d hψcd.continuous hψcs
        have heq : ∀ n, ∫ z, ‖(d.μn n z - μ z) * ψ z‖ ^ 2
            = ∫ z, ‖(d.μn n z - μ z) * ψ z‖ ^ 2 ∂ν := by
          intro n
          exact plwd_integral_ball_eq_real (f := fun z => ‖(d.μn n z - μ z) * ψ z‖ ^ 2)
            (fun z hz => by
              have hz0 : ψ z = 0 := by
                by_contra h
                exact hz (hψsub (subset_tsupport _ (Function.mem_support.mpr h)))
              rw [hz0, mul_zero, norm_zero]
              norm_num)
        exact h.congr' (Filter.Eventually.of_forall heq)
      have hbd : ∀ n, ‖∫ z, dz (d.Fn n : ℂ → ℂ) z * ((d.μn n z - μ z) * ψ z) ∂ν‖
          ≤ Real.sqrt (max C₀ 0) * Real.sqrt (∫ z, ‖(d.μn n z - μ z) * ψ z‖ ^ 2 ∂ν) := by
        intro n
        refine (plwd_norm_integral_mul_le (plwd_memLp_dz d R hR n)
          (plwd_memLp_mu_sub_mul hμ d hψm n)).trans ?_
        exact mul_le_mul_of_nonneg_right
          (Real.sqrt_le_sqrt (le_trans (hC₀ n) (le_max_left _ _))) (Real.sqrt_nonneg _)
      refine squeeze_zero (fun n => norm_nonneg _) (fun n => hbd n) ?_
      have hs : Filter.Tendsto (fun n => Real.sqrt (∫ z, ‖(d.μn n z - μ z) * ψ z‖ ^ 2 ∂ν))
          Filter.atTop (nhds (Real.sqrt 0)) :=
        Real.continuous_sqrt.tendsto 0 |>.comp hb
      simpa using hs.const_mul (Real.sqrt (max C₀ 0))
    have hz2 : Filter.Tendsto (fun n => ∫ z, dz (d.Fn n : ℂ → ℂ) z * (μ z * ψ z) ∂ν)
        Filter.atTop (nhds (∫ z, D z * (μ z * ψ z) ∂ν)) := by
      refine plwd_tendsto_integral_mul_of_testSpace (R := R)
        (Work.MRMT.Found.PLWD.denseRange_testLp R) (fun n => plwd_memLp_dz d R hR n) hDm
        (fun n => hC₀ n) ?_ (plwd_memLp_mu_mul hμ hψm)
      intro ψ'
      have hstep : Filter.Tendsto (fun n => ∫ z, dz (d.Fn n : ℂ → ℂ) z * (ψ' : ℂ → ℂ) z ∂ν)
          Filter.atTop (nhds (-∫ z, (d.φ : ℂ → ℂ) z * dz (ψ' : ℂ → ℂ) z)) := by
        have heq : ∀ n, ∫ z, dz (d.Fn n : ℂ → ℂ) z * (ψ' : ℂ → ℂ) z ∂ν
            = -∫ z, (d.Fn n : ℂ → ℂ) z * dz (ψ' : ℂ → ℂ) z := by
          intro n
          rw [← plwd_integral_ball_eq (f := fun z =>
            dz ((d.Fn n : ℂ ≃ₜ ℂ) : ℂ → ℂ) z * (ψ' : ℂ → ℂ) z)
            (plwd_support_mul_subset ψ'.2.2.2 (fun z => dz ((d.Fn n : ℂ ≃ₜ ℂ) : ℂ → ℂ) z))]
          exact (neg_eq_iff_eq_neg.mpr
            (Work.MRMT.Beltrami.integral_mul_dz_eq_neg (d.contDiff_Fn n) ψ'.2.1 ψ'.2.2.1)).symm
        have hconv := plwd_tendsto_integral_Fn_mul d (plwd_continuous_dz ψ'.2.1)
          (plwd_hasCompactSupport_dz ψ') (plwd_support_dz_subset_closedBall ψ')
        have hconv2 : Filter.Tendsto (fun n => -∫ z, (d.Fn n : ℂ → ℂ) z * dz (ψ' : ℂ → ℂ) z)
            Filter.atTop (nhds (-∫ z, (d.φ : ℂ → ℂ) z * dz (ψ' : ℂ → ℂ) z)) := hconv.neg
        exact hconv2.congr' (Filter.Eventually.of_forall fun n => (heq n).symm)
      have hfin : ∫ z, D z * (ψ' : ℂ → ℂ) z ∂ν = -∫ z, (d.φ : ℂ → ℂ) z * dz (ψ' : ℂ → ℂ) z := by
        rw [← plwd_integral_ball_eq (f := fun z => D z * (ψ' : ℂ → ℂ) z)
          (plwd_support_mul_subset ψ'.2.2.2 (fun z => D z))]
        exact hD ψ'
      rw [hfin]
      exact hstep
    have hsum := hz1.add hz2
    have hsum' : Filter.Tendsto (fun n => (∫ z, dz (d.Fn n : ℂ → ℂ) z * ((d.μn n z - μ z) * ψ z) ∂ν)
        + (∫ z, dz (d.Fn n : ℂ → ℂ) z * (μ z * ψ z) ∂ν)) Filter.atTop
        (nhds (∫ z, D z * (μ z * ψ z) ∂ν)) := by
      simpa using hsum
    have hstep1 : Filter.Tendsto (fun n => ∫ z, d.μn n z * dz (d.Fn n : ℂ → ℂ) z * ψ z) Filter.atTop
        (nhds (∫ z, D z * (μ z * ψ z) ∂ν)) :=
      hsum'.congr' (Filter.Eventually.of_forall fun n => (hsingle n).symm)
    have hlim : ∫ z, D z * (μ z * ψ z) ∂ν = ∫ z, μ z * D z * ψ z := by
      rw [plwd_integral_ball_eq (f := fun z => μ z * D z * ψ z)
        (plwd_support_mul_subset hψsub (fun z => μ z * D z))]
      refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
      ring
    rwa [hlim] at hstep1
  exact tendsto_nhds_unique h2 h1

/-! ## The main theorem -/

theorem principalData_local_weak_derivative {μ : ℂ → ℂ} (hμ : Work.MRMT.Found.Admissible μ)
    (d : Work.MRMT.Found.PrincipalData μ) (R : ℝ) (hR : 0 < R) :
    ∃ D : ℂ → ℂ,
      MeasureTheory.IntegrableOn (fun z => ‖D z‖ ^ 2) (Metric.ball 0 R) MeasureTheory.volume ∧
      (∀ ψ : ℂ → ℂ, ContDiff ℝ 1 ψ → HasCompactSupport ψ → tsupport ψ ⊆ Metric.ball 0 R →
        ∫ z, D z * ψ z = -∫ z, (d.φ : ℂ → ℂ) z * Work.MRMT.dz ψ z) ∧
      (∀ ψ : ℂ → ℂ, ContDiff ℝ 1 ψ → HasCompactSupport ψ → tsupport ψ ⊆ Metric.ball 0 R →
        ∫ z, μ z * D z * ψ z = -∫ z, (d.φ : ℂ → ℂ) z * Work.MRMT.dzbar ψ z) := by
  classical
  obtain ⟨C₀, hC₀⟩ := uniform_dz_bound hμ d R hR
  have hφloc : LocallyIntegrable (d.φ : ℂ → ℂ) (volume : Measure ℂ) :=
    d.φ.continuous.locallyIntegrable
  have hbd : ∀ ψ : testSpace R, ‖∫ z, (d.φ : ℂ → ℂ) z * dz (ψ : ℂ → ℂ) z‖
      ≤ Real.sqrt (max C₀ 0) * ‖testLp R ψ‖ := by
    intro ψ
    have hconv := plwd_tendsto_integral_Fn_mul d (plwd_continuous_dz ψ.2.1)
      (plwd_hasCompactSupport_dz ψ) (plwd_support_dz_subset_closedBall ψ)
    refine le_of_tendsto hconv.norm (Filter.Eventually.of_forall fun n => ?_)
    rw [Work.MRMT.Beltrami.integral_mul_dz_eq_neg (d.contDiff_Fn n) ψ.2.1 ψ.2.2.1, norm_neg]
    rw [plwd_integral_ball_eq (plwd_support_mul_subset ψ.2.2.2
      (fun z => dz ((d.Fn n : ℂ ≃ₜ ℂ) : ℂ → ℂ) z))]
    refine (plwd_norm_integral_mul_le (plwd_memLp_dz d R hR n)
      (memLp_of_mem_testSpace ψ.2)).trans ?_
    have hnormψ : Real.sqrt (∫ z, ‖(ψ : ℂ → ℂ) z‖ ^ 2
        ∂((volume : Measure ℂ).restrict (Metric.ball 0 R))) = ‖testLp R ψ‖ := by
      rw [← plwd_norm_testLp R ψ, Real.sqrt_sq (norm_nonneg _)]
    rw [hnormψ]
    exact mul_le_mul_of_nonneg_right
      (Real.sqrt_le_sqrt (le_trans (hC₀ n) (le_max_left _ _))) (norm_nonneg _)
  obtain ⟨D, hDm, hD⟩ := Work.MRMT.Found.PLWD.exists_weak_dz_deriv_of_bound_memLp
    (φ := (d.φ : ℂ → ℂ)) hφloc (Real.sqrt_nonneg _) (Work.MRMT.Found.PLWD.denseRange_testLp R) hbd
  refine ⟨D, ?_, ?_, ?_⟩
  · exact (memLp_two_iff_integrable_sq_norm hDm.aestronglyMeasurable).mp hDm
  · intro ψ a b c
    exact hD ⟨ψ, a, b, c⟩
  · intro ψ a b c
    exact plwd_second_identity hμ d hR hDm hD ψ a b c

end Work.MRMT.Found
