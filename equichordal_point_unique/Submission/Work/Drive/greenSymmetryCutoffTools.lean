import Mathlib
import Submission.Work.SimplyConnected.ABS.Defs
import Submission.Work.Drive.greenSymmetryCutoff
import Submission.Work.Kernel.pairingPoleTools

/-!
# Tools for the two-cutoff route to the symmetry of the Green function

Definitions and the chartwise smoothness lemmas for the "regularised Green function" used in
`Submission/Work/Drive/greenSymmetry_cutoff_bound.lean`: at a pole the Green function is made `C¹`
by adding `χ · log ‖c(·) - c(pole)‖` (a bump times the chart logarithm), which cancels the
logarithmic pole exactly; the resulting function is smooth in every chart.
-/

open MeasureTheory Set Filter
open scoped Manifold Topology Gradient ContDiff

noncomputable section

set_option linter.unusedSectionVars false

namespace Work.Drive

variable {X : Type*} [TopologicalSpace X] [T2Space X] [ChartedSpace ℂ X]

/-- The chart logarithm `x ↦ log ‖c x - c x₀‖`. -/
noncomputable def chartLog (x₀ : X) : X → ℝ :=
  fun x => Real.log ‖(chartAt ℂ x₀) x - (chartAt ℂ x₀) x₀‖

/-- The regulariser at a pole: a bump times the chart logarithm. -/
noncomputable def poleReg (x₀ : X) (χ : X → ℝ) : X → ℝ := fun x => χ x * chartLog x₀ x

variable [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]

/-- **Chartwise smoothness of the chart logarithm away from the pole.** -/
theorem chartLog_contDiffAt_chart {c₀ : X} {y : X} {x : X}
    (hx : x ∈ (chartAt ℂ y).source) (hxsrc : x ∈ (chartAt ℂ c₀).source) (hxc : x ≠ c₀) :
    ContDiffAt ℝ 1 (chartLog c₀ ∘ (chartAt ℂ y).symm) ((chartAt ℂ y) x) := by
  classical
  set cy : OpenPartialHomeomorph X ℂ := chartAt ℂ y with hcy
  set q : ℂ := cy x with hq
  have hqtgt : q ∈ cy.target := by rw [hq]; exact cy.map_source hx
  set p : ℂ := (chartAt ℂ c₀) c₀ with hp
  have hpx : (chartAt ℂ c₀) x ≠ p := by
    intro hcon
    have h1 : (chartAt ℂ c₀).symm ((chartAt ℂ c₀) x) = (chartAt ℂ c₀).symm p := congrArg _ hcon
    rw [(chartAt ℂ c₀).left_inv hxsrc, hp,
      (chartAt ℂ c₀).left_inv (mem_chart_source ℂ c₀)] at h1
    exact hxc h1
  have hsrc : cy.symm q ∈ (chartAt ℂ c₀).source := by
    rw [hq, cy.left_inv hx]; exact hxsrc
  have hana : AnalyticAt ℂ (fun w : ℂ => (chartAt ℂ c₀) (cy.symm w)) q :=
    Submission.analyticAt_transition_of_mem_atlas (chart_mem_atlas ℂ c₀)
      (by rw [hcy]; exact chart_mem_atlas ℂ y) q hqtgt hsrc
  have hcd1 : ContDiffAt ℝ 1 (fun w : ℂ => (chartAt ℂ c₀) (cy.symm w) - p) q :=
    (hana.contDiffAt.sub contDiffAt_const).restrict_scalars ℝ
  have hne : (fun w : ℂ => (chartAt ℂ c₀) (cy.symm w) - p) q ≠ 0 := by
    show (chartAt ℂ c₀) (cy.symm q) - p ≠ 0
    rw [hq, cy.left_inv hx]
    exact sub_ne_zero.mpr hpx
  have hnorm : ContDiffAt ℝ 1 (fun w : ℂ => ‖(chartAt ℂ c₀) (cy.symm w) - p‖) q :=
    ContDiffAt.norm ℝ hcd1 hne
  have hlog : ContDiffAt ℝ 1 (fun w : ℂ => Real.log ‖(chartAt ℂ c₀) (cy.symm w) - p‖) q :=
    hnorm.log (by
      show ‖(chartAt ℂ c₀) (cy.symm q) - p‖ ≠ 0
      rw [hq, cy.left_inv hx]
      exact norm_ne_zero_iff.mpr (sub_ne_zero.mpr hpx))
  refine hlog.congr_of_eventuallyEq ?_
  have hsrc_near : ∀ᶠ w in 𝓝 q, cy.symm w ∈ cy.source :=
    (cy.continuousAt_symm hqtgt).eventually (cy.open_source.mem_nhds (cy.map_target hqtgt))
  filter_upwards [hsrc_near] with w _
  simp only [Function.comp_apply, chartLog]
  rw [hp]


/-- **Chartwise smoothness of the regulariser away from the pole.** -/
theorem poleReg_contDiffAt_chart {c₀ : X} {χ : X → ℝ} {y : X} {x : X}
    (hχsm : ContMDiff (modelWithCornersSelf ℝ ℂ) (modelWithCornersSelf ℝ ℝ)
      ((⊤ : ℕ∞) : WithTop ℕ∞) χ)
    (hχsrc : tsupport χ ⊆ (chartAt ℂ c₀).source)
    (hx : x ∈ (chartAt ℂ y).source) (hxc : x ≠ c₀) :
    ContDiffAt ℝ 1 (poleReg c₀ χ ∘ (chartAt ℂ y).symm) ((chartAt ℂ y) x) := by
  classical
  haveI : IsManifold (modelWithCornersSelf ℝ ℂ) (⊤ : WithTop ℕ∞) X :=
    Work.SimplyConnected.ABS.isManifold_self_model_real_infty
  set cy : OpenPartialHomeomorph X ℂ := chartAt ℂ y with hcy
  set q : ℂ := cy x with hq
  have hqtgt : q ∈ cy.target := by rw [hq]; exact cy.map_source hx
  by_cases hmem : x ∈ tsupport χ
  swap
  · -- the bump vanishes near x, hence so does the regulariser
    have hzero : ∀ᶠ z in 𝓝 x, χ z * chartLog c₀ z = 0 := by
      filter_upwards [(isClosed_tsupport χ).isOpen_compl.mem_nhds hmem] with z hz
      have hz0 : χ z = 0 := image_eq_zero_of_notMem_tsupport hz
      rw [hz0, zero_mul]
    have hpre : ∀ᶠ w in 𝓝 q, (poleReg c₀ χ ∘ cy.symm) w = 0 := by
      have hxeq : cy.symm q = x := by rw [hq]; exact cy.left_inv hx
      have := (cy.continuousAt_symm hqtgt).eventually (by rwa [hxeq])
      filter_upwards [this] with w hw
      simpa only [Function.comp_apply, poleReg] using hw
    exact (contDiffAt_const (x := q) (c := (0:ℝ))).congr_of_eventuallyEq hpre
  · -- the bump does not vanish: multiply the two smooth factors
    have hxsrc : x ∈ (chartAt ℂ c₀).source := hχsrc hmem
    have hχc1 : ContDiffAt ℝ 1 (χ ∘ cy.symm) q :=
      Work.Drive.contDiffAt_comp_symm_of_contMDiff hχsm (by rw [hcy]; exact chart_mem_atlas ℂ y) hx
    have hlogc1 : ContDiffAt ℝ 1 (chartLog c₀ ∘ cy.symm) q :=
      chartLog_contDiffAt_chart (c₀ := c₀) (y := y) (x := x) hx hxsrc hxc
    have hmul : ContDiffAt ℝ 1 ((χ ∘ cy.symm) * (chartLog c₀ ∘ cy.symm)) q := hχc1.mul hlogc1
    refine hmul.congr_of_eventuallyEq ?_
    filter_upwards with w
    rfl


/-- **The regularised Green function near its pole.**  Adding the chart logarithm to a function with
the logarithmic expansion makes it agree, near the pole, with the harmonic correction. -/
theorem regFun_eq_near_pole {b : X} {g : X → ℝ} {χ : X → ℝ} (hχ1 : χ =ᶠ[𝓝 b] 1)
    {H : ℂ → ℝ} {r : ℝ} (hr : 0 < r)
    (hueq : ∀ z ∈ Metric.ball ((chartAt ℂ b) b) r,
      g ((chartAt ℂ b).symm z) = -Real.log ‖z - (chartAt ℂ b) b‖ + H z) :
    (fun x => g x + poleReg b χ x) =ᶠ[𝓝 b] (fun x => H ((chartAt ℂ b) x)) := by
  have hsrc : (chartAt ℂ b).source ∈ 𝓝 b :=
    (chartAt ℂ b).open_source.mem_nhds (mem_chart_source ℂ b)
  have hball : Metric.ball ((chartAt ℂ b) b) r ∈ 𝓝 ((chartAt ℂ b) b) :=
    Metric.isOpen_ball.mem_nhds (by rw [Metric.mem_ball, dist_self]; exact hr)
  have hpre : (chartAt ℂ b) ⁻¹' Metric.ball ((chartAt ℂ b) b) r ∈ 𝓝 b :=
    ((chartAt ℂ b).continuousAt (mem_chart_source ℂ b)).preimage_mem_nhds hball
  filter_upwards [hχ1, hsrc, hpre] with x hχ hxs hx
  have hval : g x = -Real.log ‖(chartAt ℂ b) x - (chartAt ℂ b) b‖ + H ((chartAt ℂ b) x) := by
    have := hueq ((chartAt ℂ b) x) hx
    rwa [(chartAt ℂ b).left_inv hxs] at this
  have hlog : poleReg b χ x = χ x * Real.log ‖(chartAt ℂ b) x - (chartAt ℂ b) b‖ := rfl
  rw [hlog, hχ]
  simp only [Pi.one_apply, hval]
  ring

/-- The regularised Green function is `C¹` at the pole, in every chart. -/
theorem regFun_contDiffAt_pole {b : X} {g : X → ℝ} {χ : X → ℝ} (hχ1 : χ =ᶠ[𝓝 b] 1)
    {H : ℂ → ℝ} {r : ℝ} (hr : 0 < r) (hH : ContDiffAt ℝ 1 H ((chartAt ℂ b) b))
    (hueq : ∀ z ∈ Metric.ball ((chartAt ℂ b) b) r,
      g ((chartAt ℂ b).symm z) = -Real.log ‖z - (chartAt ℂ b) b‖ + H z)
    {y : X} (hy : b ∈ (chartAt ℂ y).source) :
    ContDiffAt ℝ 1 ((fun x => g x + poleReg b χ x) ∘ (chartAt ℂ y).symm)
      ((chartAt ℂ y) b) := by
  classical
  set cy : OpenPartialHomeomorph X ℂ := chartAt ℂ y with hcy
  set q : ℂ := cy b with hq
  have hqtgt : q ∈ cy.target := by rw [hq]; exact cy.map_source hy
  -- the analytic transition at `q`
  have hsrc : cy.symm q ∈ (chartAt ℂ b).source := by
    rw [hq, cy.left_inv hy]; exact mem_chart_source ℂ b
  have hana : AnalyticAt ℂ (fun w : ℂ => (chartAt ℂ b) (cy.symm w)) q :=
    Submission.analyticAt_transition_of_mem_atlas (chart_mem_atlas ℂ b)
      (by rw [hcy]; exact chart_mem_atlas ℂ y) q hqtgt hsrc
  have hbq : cy.symm q = b := by rw [hq]; exact cy.left_inv hy
  have hval : (chartAt ℂ b) (cy.symm q) = (chartAt ℂ b) b := by rw [hbq]
  have hH' : ContDiffAt ℝ 1 H ((chartAt ℂ b) (cy.symm q)) := hval ▸ hH
  have hcomp : ContDiffAt ℝ 1 (fun w : ℂ => H ((chartAt ℂ b) (cy.symm w))) q :=
    ContDiffAt.comp q hH' (hana.contDiffAt.restrict_scalars ℝ)
  -- eventual equality of the chart representatives
  refine hcomp.congr_of_eventuallyEq ?_
  have hev := regFun_eq_near_pole (b := b) (g := g) (χ := χ) hχ1 hr hueq
  have hcont : ContinuousAt cy.symm q := cy.continuousAt_symm hqtgt
  have hev' : ∀ᶠ w in 𝓝 q, (g + poleReg b χ) (cy.symm w) = H ((chartAt ℂ b) (cy.symm w)) := by
    have hb : cy.symm q = b := by rw [hq]; exact cy.left_inv hy
    exact hcont.eventually (by rwa [hb])
  filter_upwards [hev'] with w hw
  simpa only [Function.comp_apply, Pi.add_apply] using hw


/-- **Chartwise `C¹` data of a smooth function of a harmonic function.** -/
theorem contDiffAt_comp_stepCutoff {Ω : Set X} {b : X} {g : X → ℝ} {σ M : ℝ}
    (hσ : 0 < σ) (hσM : 2 * σ ≤ M)
    (hg : Submission.HarmonicOnX g (Ω \ {b}))
    (hgt : ∀ᶠ x in 𝓝 b, M ≤ g x)
    {y : X} {x : X} (hx : x ∈ (chartAt ℂ y).source) (hxΩ : x ∈ Ω) :
    ContDiffAt ℝ 1 ((fun x => stepCutoff σ (g x)) ∘ (chartAt ℂ y).symm)
      ((chartAt ℂ y) x) := by
  by_cases hxb : x = b
  swap
  · -- at a smoothness point of `g`
    have hx' : x ∈ Ω \ {b} := ⟨hxΩ, by simpa [Set.mem_singleton_iff] using hxb⟩
    have hg2 : ContDiffAt ℝ 2 (g ∘ (chartAt ℂ y).symm) ((chartAt ℂ y) x) :=
      ((Submission.HarmonicOnXAt_iff_chart (u := g) (x := x) (y := y) hx).mp (hg x hx')).1
    have hg1 : ContDiffAt ℝ 1 (g ∘ (chartAt ℂ y).symm) ((chartAt ℂ y) x) := hg2.of_le (by norm_num)
    have hstep : ContDiffAt ℝ 1 (stepCutoff σ) ((g ∘ (chartAt ℂ y).symm) ((chartAt ℂ y) x)) :=
      (contDiff_stepCutoff σ (n := 1)).contDiffAt
    have hcomp := ContDiffAt.comp ((chartAt ℂ y) x) hstep hg1
    rwa [show stepCutoff σ ∘ (g ∘ (chartAt ℂ y).symm)
      = (fun x => stepCutoff σ (g x)) ∘ (chartAt ℂ y).symm from rfl] at hcomp
  · -- at the pole the cutoff is eventually `1`
    have hgt' : ∀ᶠ z in 𝓝 x, M ≤ g z := by rw [hxb]; exact hgt
    have hconst : (fun z : X => stepCutoff σ (g z)) =ᶠ[𝓝 x] (fun _ => (1 : ℝ)) := by
      filter_upwards [hgt'] with z hz
      exact stepCutoff_eq_one_of_two_mul_le hσ (le_trans hσM hz)
    have hsym : (chartAt ℂ y).symm ((chartAt ℂ y) x) = x := (chartAt ℂ y).left_inv hx
    have hev : ((fun z : X => stepCutoff σ (g z)) ∘ (chartAt ℂ y).symm)
        =ᶠ[𝓝 ((chartAt ℂ y) x)] (fun _ => (1 : ℝ)) := by
      filter_upwards [((chartAt ℂ y).continuousAt_symm ((chartAt ℂ y).map_source hx)).eventually
        (by rw [hsym]; exact hconst)] with z hz
      simpa only [Function.comp_apply] using hz
    exact (contDiffAt_const (x := (chartAt ℂ y) x) (c := (1:ℝ))).congr_of_eventuallyEq hev

/-- **Chartwise `C¹` data of the regularised Green function away from the pole.** -/
theorem regFun_contDiffAt_chart {Ω : Set X} {b : X} {g : X → ℝ} {χ : X → ℝ}
    (hχsm : ContMDiff (modelWithCornersSelf ℝ ℂ) (modelWithCornersSelf ℝ ℝ)
      ((⊤ : ℕ∞) : WithTop ℕ∞) χ)
    (hχsrc : tsupport χ ⊆ (chartAt ℂ b).source)
    (hg : Submission.HarmonicOnX g (Ω \ {b}))
    {y : X} {x : X} (hx : x ∈ (chartAt ℂ y).source) (hxΩ : x ∈ Ω) (hxb : x ≠ b) :
    ContDiffAt ℝ 1 ((fun x => g x + poleReg b χ x) ∘ (chartAt ℂ y).symm)
      ((chartAt ℂ y) x) := by
  have hx' : x ∈ Ω \ {b} := ⟨hxΩ, by simpa [Set.mem_singleton_iff] using hxb⟩
  have hg1 : ContDiffAt ℝ 1 (g ∘ (chartAt ℂ y).symm) ((chartAt ℂ y) x) :=
    (((Submission.HarmonicOnXAt_iff_chart (u := g) (x := x) (y := y) hx).mp (hg x hx')).1).of_le
      (by norm_num)
  have hp1 : ContDiffAt ℝ 1 (poleReg b χ ∘ (chartAt ℂ y).symm) ((chartAt ℂ y) x) :=
    poleReg_contDiffAt_chart hχsm hχsrc hx hxb
  rw [show ((fun x => g x + poleReg b χ x) ∘ (chartAt ℂ y).symm)
      = (g ∘ (chartAt ℂ y).symm) + (poleReg b χ ∘ (chartAt ℂ y).symm) from rfl]
  exact hg1.add hp1



/-! ## The primitives of the step cutoff

`stepPrim σ` is the primitive of `stepCutoff σ` and `stepComp σ` the primitive of `1 - stepCutoff σ`;
their sum is the identity on `[0, ∞)` and both are constants above `2σ`. -/

/-- The primitive of the step cutoff: `(stepPrim σ)' = stepCutoff σ`, `stepPrim σ 0 = 0`. -/
noncomputable def stepPrim (σ : ℝ) : ℝ → ℝ := fun t => ∫ s in (0 : ℝ)..t, stepCutoff σ s

/-- The primitive of `1 - stepCutoff σ`: `(stepComp σ)' = 1 - stepCutoff σ`, `stepComp σ 0 = 0`. -/
noncomputable def stepComp (σ : ℝ) : ℝ → ℝ :=
  fun t => ∫ s in (0 : ℝ)..t, (1 - stepCutoff σ s)

theorem stepPrim_zero (σ : ℝ) : stepPrim σ 0 = 0 := by simp [stepPrim]

theorem stepComp_zero (σ : ℝ) : stepComp σ 0 = 0 := by simp [stepComp]

theorem hasDerivAt_stepPrim (σ : ℝ) (t : ℝ) :
    HasDerivAt (stepPrim σ) (stepCutoff σ t) t := by
  have hc : Continuous (stepCutoff σ) := (contDiff_stepCutoff σ (n := 1)).continuous
  exact intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable 0 t)
    (Continuous.stronglyMeasurableAtFilter hc volume (𝓝 t)) hc.continuousAt

theorem hasDerivAt_stepComp (σ : ℝ) (t : ℝ) :
    HasDerivAt (stepComp σ) (1 - stepCutoff σ t) t := by
  have hc : Continuous (fun s => (1 : ℝ) - stepCutoff σ s) :=
    continuous_const.sub (contDiff_stepCutoff σ (n := 1)).continuous
  exact intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable 0 t)
    (Continuous.stronglyMeasurableAtFilter hc volume (𝓝 t)) hc.continuousAt

theorem differentiable_stepPrim (σ : ℝ) : Differentiable ℝ (stepPrim σ) :=
  fun t => (hasDerivAt_stepPrim σ t).differentiableAt

theorem differentiable_stepComp (σ : ℝ) : Differentiable ℝ (stepComp σ) :=
  fun t => (hasDerivAt_stepComp σ t).differentiableAt

/-- The two primitives add up to the identity: `θ` is defined as `t·Ξ t - stepPrim t`. -/
theorem thetaCutoff_add_stepPrim (σ t : ℝ) :
    thetaCutoff σ t + stepPrim σ t = t * stepCutoff σ t := by
  rw [thetaCutoff, stepPrim]; ring

theorem stepPrim_add_stepComp (σ : ℝ) (t : ℝ) :
    stepPrim σ t + stepComp σ t = t := by
  have h1 : stepComp σ t = (∫ s in (0:ℝ)..t, (1 : ℝ)) - ∫ s in (0:ℝ)..t, stepCutoff σ s := by
    rw [stepComp]
    exact intervalIntegral.integral_sub (intervalIntegrable_const)
      ((contDiff_stepCutoff σ (n := 1)).continuous.intervalIntegrable 0 t)
  rw [stepPrim, h1, intervalIntegral.integral_const]
  simp only [sub_zero, zero_mul, mul_one]
  ring

theorem stepComp_nonneg (σ : ℝ) {t : ℝ} (ht : 0 ≤ t) : 0 ≤ stepComp σ t := by
  rw [stepComp]
  refine intervalIntegral.integral_nonneg ht fun s _ => ?_
  exact sub_nonneg.mpr (stepCutoff_le_one σ s)

theorem stepComp_eq_of_two_mul_le {σ : ℝ} (hσ : 0 < σ) {t : ℝ} (h : 2 * σ ≤ t) :
    stepComp σ t = 2 * σ - ∫ s in (0 : ℝ)..(2 * σ), stepCutoff σ s := by
  rw [stepComp]
  have hint : ∀ a b : ℝ, IntervalIntegrable (fun s => (1 : ℝ) - stepCutoff σ s) volume a b :=
    fun a b => (continuous_const.sub
      (contDiff_stepCutoff σ (n := 1)).continuous).intervalIntegrable a b
  have hsplit : (∫ s in (0 : ℝ)..t, ((1 : ℝ) - stepCutoff σ s))
      = (∫ s in (0 : ℝ)..(2 * σ), ((1 : ℝ) - stepCutoff σ s))
        + ∫ s in (2 * σ)..t, ((1 : ℝ) - stepCutoff σ s) :=
    (intervalIntegral.integral_add_adjacent_intervals (hint _ _) (hint _ _)).symm
  have hzero : (∫ s in (2 * σ)..t, ((1 : ℝ) - stepCutoff σ s)) = 0 := by
    have hcongr : (∫ s in (2 * σ)..t, ((1 : ℝ) - stepCutoff σ s))
        = ∫ s in (2 * σ)..t, (0 : ℝ) := by
      apply intervalIntegral.integral_congr
      intro s hs
      rw [Set.uIcc_of_le h] at hs
      simp only [Pi.sub_apply, Pi.zero_apply]
      rw [stepCutoff_eq_one_of_two_mul_le hσ hs.1]
      ring
    rw [hcongr]; simp
  rw [hsplit, hzero, add_zero]
  have h1 : (∫ s in (0 : ℝ)..(2 * σ), ((1 : ℝ) - stepCutoff σ s))
      = (∫ s in (0 : ℝ)..(2 * σ), (1 : ℝ))
        - ∫ s in (0 : ℝ)..(2 * σ), stepCutoff σ s :=
    intervalIntegral.integral_sub intervalIntegrable_const
      ((contDiff_stepCutoff σ (n := 1)).continuous.intervalIntegrable 0 (2 * σ))
  rw [h1, intervalIntegral.integral_const]
  simp

/-- Above `2σ` the cutoff θ equals the complementary primitive. -/
theorem thetaCutoff_eq_stepComp {σ : ℝ} (hσ : 0 < σ) {t : ℝ} (h : 2 * σ ≤ t) :
    thetaCutoff σ t = stepComp σ t := by
  have h1 := thetaCutoff_add_stepPrim σ t
  have h2 := stepPrim_add_stepComp σ t
  have h3 : stepCutoff σ t = 1 := stepCutoff_eq_one_of_two_mul_le hσ h
  rw [h3, mul_one] at h1
  linarith


/-- **The test function of the two-cutoff route**: a global cutoff, the level cutoff of `g` and the
regularised Green function `g + χ · log ‖c(·) - c b‖`. -/
noncomputable def cutoffTest (σ : ℝ) (b : X) (χ w g : X → ℝ) : X → ℝ :=
  fun x => w x * (stepCutoff σ (g x) * (g x + poleReg b χ x))

theorem cutoffTest_data {Ω K : Set X} {b : X} {g : X → ℝ} {χ w : X → ℝ} {σ M : ℝ} {H : ℂ → ℝ}
    {r : ℝ} (hσ : 0 < σ) (hσM : 2 * σ ≤ M)
    (hg : Work.SimplyConnected.ABS.IsGreenOn Ω b g)
    (hχsm : ContMDiff (modelWithCornersSelf ℝ ℂ) (modelWithCornersSelf ℝ ℝ)
      ((⊤ : ℕ∞) : WithTop ℕ∞) χ)
    (hχsrc : tsupport χ ⊆ (chartAt ℂ b).source)
    (hχ1 : χ =ᶠ[𝓝 b] 1)
    (hr : 0 < r) (hH : ContDiffAt ℝ 1 H ((chartAt ℂ b) b))
    (hueq : ∀ z ∈ Metric.ball ((chartAt ℂ b) b) r,
      g ((chartAt ℂ b).symm z) = -Real.log ‖z - (chartAt ℂ b) b‖ + H z)
    (hgt : ∀ᶠ x in 𝓝 b, M ≤ g x)
    (hwsm : ContMDiff (modelWithCornersSelf ℝ ℂ) (modelWithCornersSelf ℝ ℝ)
      ((⊤ : ℕ∞) : WithTop ℕ∞) w)
    (hwsupp : tsupport w ⊆ Ω)
    (hKout : ∀ x ∈ Ω, x ∉ K → (fun z => stepCutoff σ (g z)) =ᶠ[𝓝 x] 0) :
    (∀ y, Work.Drive.ChartDiff (chartAt ℂ y) (cutoffTest σ b χ w g) Ω) ∧
      (∀ y, ∀ x ∈ (chartAt ℂ y).source,
        ContDiffAt ℝ 1 ((cutoffTest σ b χ w g) ∘ (chartAt ℂ y).symm) ((chartAt ℂ y) x)) ∧
      tsupport (cutoffTest σ b χ w g) ⊆ K ∧ tsupport (cutoffTest σ b χ w g) ⊆ Ω := by
  haveI : IsManifold (modelWithCornersSelf ℝ ℂ) (⊤ : WithTop ℕ∞) X :=
    Work.SimplyConnected.ABS.isManifold_self_model_real_infty
  set Ψ : X → ℝ := cutoffTest σ b χ w g with hΨ
  -- the chartwise `C¹` data
  have hmain : ∀ y : X, ∀ x ∈ (chartAt ℂ y).source,
      ContDiffAt ℝ 1 (Ψ ∘ (chartAt ℂ y).symm) ((chartAt ℂ y) x) := by
    intro y x hx
    have hxtgt : (chartAt ℂ y) x ∈ (chartAt ℂ y).target := (chartAt ℂ y).map_source hx
    by_cases hxw : x ∈ tsupport w
    swap
    · -- the cutoff `w` vanishes near `x`
      have hz0 : ∀ᶠ z in 𝓝 x, w z = 0 := by
        filter_upwards [(isClosed_tsupport w).isOpen_compl.mem_nhds hxw] with z hz
        exact image_eq_zero_of_notMem_tsupport hz
      have hev : Ψ =ᶠ[𝓝 x] (fun _ => (0 : ℝ)) := by
        filter_upwards [hz0] with z hz
        simp only [hΨ, cutoffTest, hz, Pi.zero_apply, zero_mul]
      have hsym : (chartAt ℂ y).symm ((chartAt ℂ y) x) = x := (chartAt ℂ y).left_inv hx
      have hev' : (Ψ ∘ (chartAt ℂ y).symm) =ᶠ[𝓝 ((chartAt ℂ y) x)] (fun _ => (0 : ℝ)) := by
        filter_upwards [((chartAt ℂ y).continuousAt_symm hxtgt).eventually (by rw [hsym]; exact hev)]
          with z hz
        simpa only [Function.comp_apply] using hz
      exact (contDiffAt_const (x := (chartAt ℂ y) x) (c := (0:ℝ))).congr_of_eventuallyEq hev'
    · -- inside the support of `w`
      have hxΩ : x ∈ Ω := hwsupp hxw
      have h1 : ContDiffAt ℝ 1 (w ∘ (chartAt ℂ y).symm) ((chartAt ℂ y) x) :=
        Work.Drive.contDiffAt_comp_symm_of_contMDiff hwsm (chart_mem_atlas ℂ y) hx
      have h2 : ContDiffAt ℝ 1 ((fun z => stepCutoff σ (g z)) ∘ (chartAt ℂ y).symm)
          ((chartAt ℂ y) x) :=
        contDiffAt_comp_stepCutoff (Ω := Ω) (b := b) hσ hσM hg.2.1 hgt hx hxΩ
      have h3 : ContDiffAt ℝ 1 ((fun z => g z + poleReg b χ z) ∘ (chartAt ℂ y).symm)
          ((chartAt ℂ y) x) := by
        by_cases hxb : x = b
        · rw [hxb] at hx ⊢
          exact regFun_contDiffAt_pole (b := b) (g := g) (χ := χ) hχ1 hr hH hueq hx
        · exact regFun_contDiffAt_chart (Ω := Ω) (b := b) (g := g) (χ := χ)
            hχsm hχsrc hg.2.1 hx hxΩ hxb
      show ContDiffAt ℝ 1 ((fun x : X => w x * (stepCutoff σ (g x) * (g x + poleReg b χ x)))
          ∘ (chartAt ℂ y).symm) ((chartAt ℂ y) x)
      rw [show ((fun x : X => w x * (stepCutoff σ (g x) * (g x + poleReg b χ x)))
            ∘ (chartAt ℂ y).symm)
          = (w ∘ (chartAt ℂ y).symm)
            * (((fun z : X => stepCutoff σ (g z)) ∘ (chartAt ℂ y).symm)
              * ((fun z : X => g z + poleReg b χ z) ∘ (chartAt ℂ y).symm)) from rfl]
      exact h1.mul (h2.mul h3)
  refine ⟨fun y x hx => (hmain y x hx.2).differentiableAt (by norm_num), hmain, ?_, ?_⟩
  · -- support inside `K`
    have hKc : ∀ x, x ∉ K → x ∉ tsupport Ψ := by
      intro x hxK
      rw [notMem_tsupport_iff_eventuallyEq]
      by_cases hxw : x ∈ tsupport w
      · filter_upwards [hKout x (hwsupp hxw) hxK] with y hy
        have hy' : stepCutoff σ (g y) = 0 := by simpa using hy
        show cutoffTest σ b χ w g y = 0
        rw [show cutoffTest σ b χ w g y
          = w y * (stepCutoff σ (g y) * (g y + poleReg b χ y)) from rfl]
        rw [hy']
        ring
      · have hz0 : w =ᶠ[𝓝 x] 0 := notMem_tsupport_iff_eventuallyEq.mp hxw
        filter_upwards [hz0] with z hz
        have hz' : w z = 0 := by simpa using hz
        show cutoffTest σ b χ w g z = 0
        rw [show cutoffTest σ b χ w g z
          = w z * (stepCutoff σ (g z) * (g z + poleReg b χ z)) from rfl]
        rw [hz']
        ring
    intro x hx
    by_contra hxK
    exact hKc x hxK hx
  · -- support inside `Ω`
    intro x hx
    exact hwsupp (tsupport_mul_subset_left hx)



theorem stepCutoff_pos_iff {σ : ℝ} (hσ : 0 < σ) (t : ℝ) :
    0 < stepCutoff σ t ↔ σ < t := by
  rw [stepCutoff]
  constructor
  · intro h
    by_contra hcon
    have h1 : t / σ - 1 ≤ 0 := by
      rw [sub_nonpos, div_le_one hσ]; exact le_of_not_gt hcon
    rw [Real.smoothTransition.zero_of_nonpos h1] at h
    exact lt_irrefl 0 h
  · intro h
    exact Real.smoothTransition.pos_of_pos (by rw [sub_pos, one_lt_div hσ]; exact h)

theorem stepCutoff_eq_zero_iff {σ : ℝ} (hσ : 0 < σ) (t : ℝ) :
    stepCutoff σ t = 0 ↔ t ≤ σ := by
  constructor
  · intro h
    by_contra hcon
    have h1 : 0 < stepCutoff σ t := (stepCutoff_pos_iff hσ t).mpr (lt_of_not_ge hcon)
    rw [h] at h1
    exact lt_irrefl 0 h1
  · exact stepCutoff_eq_zero_of_le hσ

/-- The cutoff θ is `C¹`. -/
theorem contDiff_thetaCutoff {σ : ℝ} (hσ : 0 < σ) : ContDiff ℝ 1 (thetaCutoff σ) := by
  rw [contDiff_one_iff_deriv]
  refine ⟨fun t => (hasDerivAt_thetaCutoff hσ t).differentiableAt, ?_⟩
  have hderiv : deriv (thetaCutoff σ) = fun t => t * deriv (stepCutoff σ) t := by
    funext t
    exact (hasDerivAt_thetaCutoff hσ t).deriv
  rw [hderiv]
  exact continuous_id.mul ((contDiff_stepCutoff σ (n := 1)).continuous_deriv (by norm_num))

/-- The primitive bound `∫_0^t Ξ ≤ t` for `t ≥ 0`. -/
theorem integral_stepCutoff_le_self {σ : ℝ} (hσ : 0 < σ) {t : ℝ} (ht : 0 ≤ t) :
    (∫ s in (0 : ℝ)..t, stepCutoff σ s) ≤ t := by
  have h3 : (∫ s in (0 : ℝ)..t, stepCutoff σ s) ≤ ∫ s in (0 : ℝ)..t, (1 : ℝ) :=
    intervalIntegral.integral_mono_on ht
      ((contDiff_stepCutoff σ (n := 1)).continuous.intervalIntegrable 0 t)
      intervalIntegrable_const
      (fun s _ => stepCutoff_le_one σ s)
  rwa [intervalIntegral.integral_const, sub_zero, smul_eq_mul, mul_one] at h3

/-- The intermediate value `c_σ` is at most `2σ`. -/
theorem thetaCutoff_le_two_mul {σ t : ℝ} (hσ : 0 < σ) :
    thetaCutoff σ t ≤ 2 * σ := by
  rcases le_or_gt t σ with h | h
  · rw [thetaCutoff_eq_zero_of_le hσ h]
    linarith
  rcases le_or_gt t (2 * σ) with h2 | h2
  · have ht : 0 < t := lt_trans hσ h
    have h1 : thetaCutoff σ t ≤ t * stepCutoff σ t := by
      rw [thetaCutoff]
      have : 0 ≤ ∫ s in (0 : ℝ)..t, stepCutoff σ s :=
        intervalIntegral.integral_nonneg ht.le fun s _ => stepCutoff_nonneg σ s
      linarith
    have h3 : t * stepCutoff σ t ≤ t := by
      have h4 := mul_le_mul_of_nonneg_left (stepCutoff_le_one σ t) ht.le
      rwa [mul_one] at h4
    linarith
  · rw [thetaCutoff_eq_of_two_mul_le hσ (le_of_lt h2)]
    have h3 := integral_stepCutoff_le_self hσ (le_of_lt (by linarith : (0:ℝ) < 2 * σ))
    have h4 : 0 ≤ ∫ s in (0 : ℝ)..(2 * σ), stepCutoff σ s :=
      intervalIntegral.integral_nonneg (by linarith) fun s _ => stepCutoff_nonneg σ s
    linarith

theorem thetaCutoff_nonneg {σ t : ℝ} (hσ : 0 < σ) (ht : 0 ≤ t) :
    0 ≤ thetaCutoff σ t := by
  rcases le_or_gt t σ with h | h
  · rw [thetaCutoff_eq_zero_of_le hσ h]
  rcases le_or_gt t (2 * σ) with h2 | h2
  · -- `tΞ t` dominates the primitive because `Ξ` is monotone
    have hmono : Monotone (stepCutoff σ) := monotone_stepCutoff hσ
    have hle : (∫ s in (0 : ℝ)..t, stepCutoff σ s) ≤ t * stepCutoff σ t := by
      have h4 : (∫ s in (0 : ℝ)..t, stepCutoff σ s)
          ≤ ∫ s in (0 : ℝ)..t, stepCutoff σ t :=
        intervalIntegral.integral_mono_on ht
          ((contDiff_stepCutoff σ (n := 1)).continuous.intervalIntegrable 0 t)
          intervalIntegrable_const
          (fun s hs => hmono hs.2)
      rwa [intervalIntegral.integral_const, sub_zero, smul_eq_mul] at h4
    rw [thetaCutoff]
    linarith
  · rw [thetaCutoff_eq_of_two_mul_le hσ (le_of_lt h2)]
    have h3 := integral_stepCutoff_le_self hσ (le_of_lt (by linarith : (0:ℝ) < 2 * σ))
    linarith


/-- **The `C¹` and support data of the test function `w · Φ(gQ)`**, for a `C¹` profile `Φ` which is
constant above `M` and vanishes below the level `σ`. -/
theorem profile_test_data {Ω K : Set X} {q : X} {gQ w : X → ℝ} {Φ : ℝ → ℝ} {σ M : ℝ}
    (hσ : 0 < σ)
    (hgQ : Work.SimplyConnected.ABS.IsGreenOn Ω q gQ)
    (hwsm : ContMDiff (modelWithCornersSelf ℝ ℂ) (modelWithCornersSelf ℝ ℝ)
      ((⊤ : ℕ∞) : WithTop ℕ∞) w)
    (hwsupp : tsupport w ⊆ Ω) (hw1 : ∀ x ∈ K, w x = 1)
    (hgt : ∀ᶠ z in 𝓝 q, M ≤ gQ z)
    (hΦ : ContDiff ℝ 1 Φ) (hΦev : ∀ x : ℝ, M ≤ x → Φ x = Φ M)
    (hΦ0 : ∀ t ≤ σ, Φ t = 0)
    (hKout : ∀ z ∈ Ω, z ∉ K → (fun y => stepCutoff σ (gQ y)) =ᶠ[𝓝 z] 0) :
    (∀ y, Work.Drive.ChartDiff (chartAt ℂ y) (fun x => w x * Φ (gQ x)) Ω) ∧
      (∀ y, ∀ x ∈ (chartAt ℂ y).source,
        ContDiffAt ℝ 1 ((fun x => w x * Φ (gQ x)) ∘ (chartAt ℂ y).symm)
          ((chartAt ℂ y) x)) ∧
      tsupport (fun x => w x * Φ (gQ x)) ⊆ K ∧
      tsupport (fun x => w x * Φ (gQ x)) ⊆ Ω := by
  haveI : IsManifold (modelWithCornersSelf ℝ ℂ) (⊤ : WithTop ℕ∞) X :=
    Work.SimplyConnected.ABS.isManifold_self_model_real_infty
  refine ⟨fun y => (Work.Kernel.chartDiff_and_contDiffAt_mul_comp (Ω := Ω) (b := q)
      (w := w) (gB := gQ) (Φ := Φ) (M := M) hwsupp hwsm hgQ.2.1 hgt hΦ hΦev y).1,
    fun y => (Work.Kernel.chartDiff_and_contDiffAt_mul_comp (Ω := Ω) (b := q)
      (w := w) (gB := gQ) (Φ := Φ) (M := M) hwsupp hwsm hgQ.2.1 hgt hΦ hΦev y).2, ?_, ?_⟩
  · -- support inside `K`
    have hKc : ∀ x, x ∉ K → x ∉ tsupport (fun x => w x * Φ (gQ x)) := by
      intro x hxK
      rw [notMem_tsupport_iff_eventuallyEq]
      by_cases hxw : x ∈ tsupport w
      · have hxΩ : x ∈ Ω := hwsupp hxw
        have h1 := hKout x hxΩ hxK
        filter_upwards [h1] with z hz
        have h2 : gQ z ≤ σ := (stepCutoff_eq_zero_iff hσ (gQ z)).mp hz
        simp [hΦ0 _ h2]
      · have hw0 : w =ᶠ[𝓝 x] 0 := notMem_tsupport_iff_eventuallyEq.mp hxw
        filter_upwards [hw0] with z hz
        simp [hz]
    intro x hx
    by_contra hxK
    exact hKc x hxK hx
  · -- support inside `Ω`
    intro x hx
    exact hwsupp (tsupport_mul_subset_left hx)


/-- **The test function `w · (Ξ(gQ) · (gP + C_p))` of the second half of the two-cutoff computation.**
Here the regulariser `C_p = poleReg p χp` is attached to the pole `p` of the *second* function, while
the level cutoff is taken in `gQ`. -/
theorem cutoffTestB_data {Ω K : Set X} {q p : X} {gQ gP w χp : X → ℝ} {σ M : ℝ}
    (hσ : 0 < σ) (hgQ : Work.SimplyConnected.ABS.IsGreenOn Ω q gQ)
    (hσM : 2 * σ ≤ M) (hgt : ∀ᶠ z in 𝓝 q, M ≤ gQ z)
    (hgP : Work.SimplyConnected.ABS.IsGreenOn Ω p gP)
    (hwsm : ContMDiff (modelWithCornersSelf ℝ ℂ) (modelWithCornersSelf ℝ ℝ)
      ((⊤ : ℕ∞) : WithTop ℕ∞) w)
    (hwsupp : tsupport w ⊆ Ω) (hw1 : ∀ x ∈ K, w x = 1)
    (hpq : p ≠ q)
    (hχpsm : ContMDiff (modelWithCornersSelf ℝ ℂ) (modelWithCornersSelf ℝ ℝ)
      ((⊤ : ℕ∞) : WithTop ℕ∞) χp)
    (hχpsrc : tsupport χp ⊆ (chartAt ℂ p).source)
    (hχp1 : χp =ᶠ[𝓝 p] 1) (hχpq : q ∉ tsupport χp)
    {H : ℂ → ℝ} {r : ℝ} (hr : 0 < r) (hH : ContDiffAt ℝ 1 H ((chartAt ℂ p) p))
    (hueq : ∀ z ∈ Metric.ball ((chartAt ℂ p) p) r,
      gP ((chartAt ℂ p).symm z) = -Real.log ‖z - (chartAt ℂ p) p‖ + H z)
    (hKout : ∀ z ∈ Ω, z ∉ K → (fun y => stepCutoff σ (gQ y)) =ᶠ[𝓝 z] 0) :
    (∀ y, Work.Drive.ChartDiff (chartAt ℂ y)
      (fun x => w x * (stepCutoff σ (gQ x) * (gP x + poleReg p χp x))) Ω) ∧
      (∀ y, ∀ x ∈ (chartAt ℂ y).source,
        ContDiffAt ℝ 1 ((fun x => w x * (stepCutoff σ (gQ x) * (gP x + poleReg p χp x)))
          ∘ (chartAt ℂ y).symm) ((chartAt ℂ y) x)) ∧
      tsupport (fun x => w x * (stepCutoff σ (gQ x) * (gP x + poleReg p χp x))) ⊆ K ∧
      tsupport (fun x => w x * (stepCutoff σ (gQ x) * (gP x + poleReg p χp x))) ⊆ Ω := by
  haveI : IsManifold (modelWithCornersSelf ℝ ℂ) (⊤ : WithTop ℕ∞) X :=
    Work.SimplyConnected.ABS.isManifold_self_model_real_infty
  have hmain : ∀ y : X, ∀ x ∈ (chartAt ℂ y).source,
      ContDiffAt ℝ 1 ((fun x => w x * (stepCutoff σ (gQ x) * (gP x + poleReg p χp x)))
        ∘ (chartAt ℂ y).symm) ((chartAt ℂ y) x) := by
    intro y x hx
    have hxtgt : (chartAt ℂ y) x ∈ (chartAt ℂ y).target := (chartAt ℂ y).map_source hx
    by_cases hxw : x ∈ tsupport w
    swap
    · have hz0 : ∀ᶠ z in 𝓝 x, w z = 0 := by
        filter_upwards [(isClosed_tsupport w).isOpen_compl.mem_nhds hxw] with z hz
        exact image_eq_zero_of_notMem_tsupport hz
      have hev : (fun z => w z * (stepCutoff σ (gQ z) * (gP z + poleReg p χp z)))
          =ᶠ[𝓝 x] (fun _ => (0 : ℝ)) := by
        filter_upwards [hz0] with z hz
        rw [hz, zero_mul]
      have hsym : (chartAt ℂ y).symm ((chartAt ℂ y) x) = x := (chartAt ℂ y).left_inv hx
      have hev' : ((fun z => w z * (stepCutoff σ (gQ z) * (gP z + poleReg p χp z)))
          ∘ (chartAt ℂ y).symm) =ᶠ[𝓝 ((chartAt ℂ y) x)] (fun _ => (0 : ℝ)) := by
        filter_upwards [((chartAt ℂ y).continuousAt_symm hxtgt).eventually (by rw [hsym]; exact hev)]
          with z hz
        simpa only [Function.comp_apply] using hz
      exact (contDiffAt_const (x := (chartAt ℂ y) x) (c := (0:ℝ))).congr_of_eventuallyEq hev'
    · have hxΩ : x ∈ Ω := hwsupp hxw
      have h1 : ContDiffAt ℝ 1 (w ∘ (chartAt ℂ y).symm) ((chartAt ℂ y) x) :=
        Work.Drive.contDiffAt_comp_symm_of_contMDiff hwsm (chart_mem_atlas ℂ y) hx
      have h2 : ContDiffAt ℝ 1 ((fun z => stepCutoff σ (gQ z)) ∘ (chartAt ℂ y).symm)
          ((chartAt ℂ y) x) :=
        contDiffAt_comp_stepCutoff (Ω := Ω) (b := q) hσ hσM hgQ.2.1 hgt hx hxΩ
      have h3 : ContDiffAt ℝ 1 ((fun z => gP z + poleReg p χp z) ∘ (chartAt ℂ y).symm)
          ((chartAt ℂ y) x) := by
        by_cases hxp : x = p
        · rw [hxp] at hx ⊢
          exact regFun_contDiffAt_pole (b := p) (g := gP) (χ := χp) hχp1 hr hH hueq hx
        · exact regFun_contDiffAt_chart (Ω := Ω) (b := p) (g := gP) (χ := χp)
            hχpsm hχpsrc hgP.2.1 hx hxΩ hxp
      show ContDiffAt ℝ 1 ((fun x : X =>
          w x * (stepCutoff σ (gQ x) * (gP x + poleReg p χp x)))
        ∘ (chartAt ℂ y).symm) ((chartAt ℂ y) x)
      rw [show ((fun x : X => w x * (stepCutoff σ (gQ x) * (gP x + poleReg p χp x)))
            ∘ (chartAt ℂ y).symm)
          = (w ∘ (chartAt ℂ y).symm)
            * (((fun z : X => stepCutoff σ (gQ z)) ∘ (chartAt ℂ y).symm)
              * ((fun z : X => gP z + poleReg p χp z) ∘ (chartAt ℂ y).symm)) from rfl]
      exact h1.mul (h2.mul h3)
  refine ⟨fun y x hx => (hmain y x hx.2).differentiableAt (by norm_num), hmain, ?_, ?_⟩
  · have hKc : ∀ x, x ∉ K → x ∉ tsupport
        (fun x => w x * (stepCutoff σ (gQ x) * (gP x + poleReg p χp x))) := by
      intro x hxK
      rw [notMem_tsupport_iff_eventuallyEq]
      by_cases hxw : x ∈ tsupport w
      · have h1 := hKout x (hwsupp hxw) hxK
        filter_upwards [h1] with z hz
        simp [hz]
      · have hw0 : w =ᶠ[𝓝 x] 0 := notMem_tsupport_iff_eventuallyEq.mp hxw
        filter_upwards [hw0] with z hz
        rw [hz, Pi.zero_apply, zero_mul]
    intro x hx
    by_contra hxK
    exact hKc x hxK hx
  · intro x hx
    exact hwsupp (tsupport_mul_subset_left hx)

end Work.Drive
