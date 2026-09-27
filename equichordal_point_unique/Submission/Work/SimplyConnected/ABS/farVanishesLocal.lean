import Mathlib
import Submission.Work.SimplyConnected.ABS.GreenSetupReg
import Submission.Work.SimplyConnected.ABS.decayStepInputs
import Submission.Work.SimplyConnected.ABS.lsc_le_of_circleSubMeanValue
import Submission.Work.SimplyConnected.ABS.limEnvelope_le_smul_of_barrier
import Submission.Work.SimplyConnected.ABS.globalizedBarrier_dev
import Submission.Work.SimplyConnected.ABS.clampedBarrierSuperharmonic
import Submission.Work.Analysis.Poisson.poissonInt_tendsto_of_eventuallyEq
import Submission.Work.SimplyConnected.ABS.globalBarrierOfLocalBarrierReg
import Submission.DirichletX

/-!
# LOCAL COPY of the Bouligand/Poisson collar barrier (namespace `FarLocal`)

This module is a verbatim copy of the body of
`Submission.Work.SimplyConnected.ABS.limEnvelope_indicator_far_vanishes` (proved by a colleague,
sorry-free), re-declared inside the namespace `Work.SimplyConnected.ABS.FarLocal` and with the
(otherwise unused) import of `Submission.Work.SimplyConnected.ABS.limEnvelope_lt_near_of_localBarrier`
dropped.

Reason for the copy: the original module imports
`Submission.Work.SimplyConnected.ABS.limEnvelope_lt_near_of_localBarrier`, which it does not use,
and that import makes it impossible for the latter module (whose file also *states* the target
`Work.SimplyConnected.ABS.limEnvelope_lt_near_of_localBarrier`) to import the far-vanishing theorem,
because Lean forbids import cycles.  The copy is placed in its own namespace so that it can be
imported together with the original without duplicate-declaration errors.  No statement or proof is
changed.
-/

/-!
# The Bouligand/Poisson collar barrier: the Envelope is small near a barrier point

`Work.SimplyConnected.ABS.limEnvelope_indicator_far_vanishes`: if `p ∈ frontier Ω` carries a local
barrier `u` (`u` superharmonic and strictly positive on `Ω ∩ V`, continuous on the open `V`,
`u p = 0`), and `K ⊆ frontier U` is a compact set with `p ∉ K`, then the limsup Perron envelope of
the region `U` with boundary datum `1_K` is `< ε` on a neighbourhood of `p` intersected with `U`.

The classical proof (Bouligand) is the *Poisson collar* barrier: put an auxiliary level `η`, let `g`
be the indicator of the "bad" collar set where `u < η` (the Bouligand datum), and let `h` be its
Poisson integral, read on `X` through the chart at `p` (the collar).  Then

`β := min (2u/η + h) 1` on the chart ball and `β := 1` outside it

is superharmonic on `U`, equals `1` on `K` (which misses the closed chart disc), and is `< ε` near
`p`: `u p = 0` while `h p = ⨍ g` is the circle average of the datum, which is small for small `η`
because the bad sets shrink to the empty set as `η ↓ 0`.  The comparison with the Perron envelope is
`Submission.limEnvelope_le_smul_of_barrier`.

The ingredients are
* the Bouligand datum, its circle integrability, the Poisson integral and its boundary behaviour
  (`blgDatum`, `circleIntegrable_blgDatum`, `collar`, `collar_tendsto_one_ball`);
* the measure estimate for the bad collar set (`badThetaSeq`, `circleAverage_blgDatum_le`,
  `exists_eta_circleAverage_lt`);
* the sphere-side inequality making the clamp invisible (`barrierCore_eventually_ge_one`) and the
  resulting superharmonicity of the barrier (`blgBarrier_superharmonic`).
-/

open Filter Set
open Classical
open scoped Topology Manifold ContDiff

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 800000

namespace Work.SimplyConnected.ABS.FarLocal

noncomputable section

variable {X : Type*} [TopologicalSpace X] [T2Space X] [PreconnectedSpace X] [ChartedSpace ℂ X]
  [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]

/-! ## The chart setup -/

lemma exists_chartBall_data' {V K : Set X} {p : X} (hVo : IsOpen V) (hpV : p ∈ V)
    (hKcomp : IsCompact K) (hpK : p ∉ K) :
    ∃ ρ : ℝ, 0 < ρ ∧
      Metric.closedBall ((chartAt ℂ p) p) ρ ⊆ (chartAt ℂ p).target ∧
      Submission.chartClosedBall (chartAt ℂ p) ((chartAt ℂ p) p) ρ ⊆ V ∧
      Disjoint (closure (Submission.chartBall (chartAt ℂ p) ((chartAt ℂ p) p) ρ)) K := by
  classical
  have hKclosed : IsClosed K := hKcomp.isClosed
  have hVo' : IsOpen (V ∩ Kᶜ) := hVo.inter hKclosed.isOpen_compl
  have hpV' : p ∈ V ∩ Kᶜ := ⟨hpV, hpK⟩
  obtain ⟨ρ, hρ, hρtgt, hρV'⟩ := exists_chartClosedBall_subset_nhds (V := V ∩ Kᶜ) hVo' hpV'
  refine ⟨ρ, hρ, hρtgt, fun x hx => (hρV' hx).1, ?_⟩
  rw [Set.disjoint_left]
  intro x hxcl hxK
  have hxcb : x ∈ Submission.chartClosedBall (chartAt ℂ p) ((chartAt ℂ p) p) ρ :=
    closure_minimal (Submission.chartBall_subset_chartClosedBall _ _ _)
      (Submission.isClosed_chartClosedBall hρtgt) hxcl
  exact (hρV' hxcb).2 hxK

/-! ## The Bouligand datum -/

def badG (c : OpenPartialHomeomorph X ℂ) (a : ℂ) (ρ : ℝ) : Set ℂ :=
  {z : ℂ | a + (ρ : ℂ) * z ∈ c.target}

def badψ (c : OpenPartialHomeomorph X ℂ) (a : ℂ) (ρ : ℝ) (z : ℂ) : X :=
  c.symm (a + (ρ : ℂ) * z)

def blgBadSet (c : OpenPartialHomeomorph X ℂ) (a : ℂ) (ρ m : ℝ) (U V : Set X)
    (u : X → ℝ) : Set ℂ :=
  Metric.sphere (0 : ℂ) 1 ∩ badG c a ρ ∩ (badψ c a ρ) ⁻¹' (U ∩ V) ∩
    (fun z : ℂ => u (badψ c a ρ z)) ⁻¹' (Set.Iio m)

def blgDatum (c : OpenPartialHomeomorph X ℂ) (a : ℂ) (ρ m : ℝ) (U V : Set X)
    (u : X → ℝ) : ℂ → ℝ :=
  (blgBadSet c a ρ m U V u).indicator (fun _ => 1)

lemma blgBadSet_subset_sphere (c : OpenPartialHomeomorph X ℂ) (a : ℂ) (ρ m : ℝ)
    (U V : Set X) (u : X → ℝ) :
    blgBadSet c a ρ m U V u ⊆ Metric.sphere (0 : ℂ) 1 := fun z hz => hz.1.1.1

lemma mem_blgBadSet {c : OpenPartialHomeomorph X ℂ} {a : ℂ} {ρ m : ℝ} {U V : Set X}
    {u : X → ℝ} {z : ℂ} :
    z ∈ blgBadSet c a ρ m U V u ↔
      ‖z‖ = 1 ∧ a + (ρ : ℂ) * z ∈ c.target ∧ badψ c a ρ z ∈ U ∩ V ∧ u (badψ c a ρ z) < m := by
  simp [blgBadSet, badG, badψ, Set.mem_preimage, and_assoc]

lemma blgDatum_nonneg (c : OpenPartialHomeomorph X ℂ) (a : ℂ) (ρ m : ℝ) (U V : Set X)
    (u : X → ℝ) (z : ℂ) :
    0 ≤ blgDatum c a ρ m U V u z := by
  unfold blgDatum
  by_cases h : z ∈ blgBadSet c a ρ m U V u <;>
    simp [Set.indicator_of_mem, Set.indicator_of_notMem, h]

lemma blgDatum_le_one (c : OpenPartialHomeomorph X ℂ) (a : ℂ) (ρ m : ℝ) (U V : Set X)
    (u : X → ℝ) (z : ℂ) :
    blgDatum c a ρ m U V u z ≤ 1 := by
  unfold blgDatum
  by_cases h : z ∈ blgBadSet c a ρ m U V u <;>
    simp [Set.indicator_of_mem, Set.indicator_of_notMem, h]

lemma blgDatum_of_mem {c : OpenPartialHomeomorph X ℂ} {a : ℂ} {ρ m : ℝ} {U V : Set X}
    {u : X → ℝ} {z : ℂ} (hz : z ∈ blgBadSet c a ρ m U V u) :
    blgDatum c a ρ m U V u z = 1 := by
  unfold blgDatum
  rw [Set.indicator_of_mem hz]

lemma measurableSet_blgBadSet {c : OpenPartialHomeomorph X ℂ} {a : ℂ} {ρ m : ℝ}
    {U V : Set X} {u : X → ℝ} (hVo : IsOpen V) (hUo : IsOpen U) (hucont : ContinuousOn u V) :
    MeasurableSet (blgBadSet c a ρ m U V u) := by
  have hG : IsOpen (badG c a ρ) := by
    unfold badG
    exact c.open_target.preimage (continuous_const.add (continuous_const.mul continuous_id))
  have hψ : ContinuousOn (badψ c a ρ) (badG c a ρ) := by
    unfold badψ badG
    exact c.continuousOn_symm.comp
      (continuous_const.add (continuous_const.mul continuous_id)).continuousOn
      (fun z hz => hz)
  have h1 : IsOpen (badG c a ρ ∩ (badψ c a ρ) ⁻¹' (U ∩ V)) :=
    hψ.isOpen_inter_preimage hG (hUo.inter hVo)
  have h2 : ContinuousOn (fun z : ℂ => u (badψ c a ρ z))
      (badG c a ρ ∩ (badψ c a ρ) ⁻¹' (U ∩ V)) := by
    refine hucont.comp (hψ.mono Set.inter_subset_left) (fun z hz => ?_)
    exact hz.2.2
  have h3 : IsOpen ((badG c a ρ ∩ (badψ c a ρ) ⁻¹' (U ∩ V)) ∩
      (fun z : ℂ => u (badψ c a ρ z)) ⁻¹' (Set.Iio m)) :=
    h2.isOpen_inter_preimage h1 isOpen_Iio
  have hset : blgBadSet c a ρ m U V u =
      Metric.sphere (0 : ℂ) 1 ∩ ((badG c a ρ ∩ (badψ c a ρ) ⁻¹' (U ∩ V)) ∩
        (fun z : ℂ => u (badψ c a ρ z)) ⁻¹' (Set.Iio m)) := by
    ext z
    simp only [blgBadSet, Set.mem_inter_iff, Set.mem_preimage]
    tauto
  rw [hset]
  exact (Metric.isClosed_sphere.measurableSet).inter h3.measurableSet

lemma measurable_blgDatum {c : OpenPartialHomeomorph X ℂ} {a : ℂ} {ρ m : ℝ}
    {U V : Set X} {u : X → ℝ} (hVo : IsOpen V) (hUo : IsOpen U) (hucont : ContinuousOn u V) :
    Measurable (blgDatum c a ρ m U V u) := by
  refine Measurable.ite ?_ measurable_const measurable_const
  exact measurableSet_blgBadSet hVo hUo hucont

lemma norm_deriv_circleMap_one (θ : ℝ) : ‖deriv (circleMap (0 : ℂ) 1) θ‖ = 1 := by
  rw [deriv_circleMap]
  simp [Complex.norm_exp]

lemma circleIntegrable_blgDatum {c : OpenPartialHomeomorph X ℂ} {a : ℂ} {ρ m : ℝ}
    {U V : Set X} {u : X → ℝ} (hVo : IsOpen V) (hUo : IsOpen U) (hucont : ContinuousOn u V) :
    CircleIntegrable (fun z : ℂ => (blgDatum c a ρ m U V u z : ℂ)) 0 1 := by
  have hvol : MeasureTheory.volume (Set.uIoc (0:ℝ) (2 * Real.pi)) < ⊤ := by
    rw [Real.volume_uIoc]; exact ENNReal.ofReal_lt_top
  have hderiv : Continuous fun θ : ℝ => deriv (circleMap (0 : ℂ) 1) θ := by
    rw [show (fun θ : ℝ => deriv (circleMap (0 : ℂ) 1) θ) =
      fun θ => circleMap (0 : ℂ) 1 θ * Complex.I from funext (fun θ => deriv_circleMap 0 1 θ)]
    exact (continuous_circleMap 0 1).mul continuous_const
  have h1 : MeasureTheory.AEStronglyMeasurable
      (fun θ : ℝ => deriv (circleMap (0 : ℂ) 1) θ)
      (MeasureTheory.volume.restrict (Set.uIoc (0:ℝ) (2 * Real.pi))) :=
    hderiv.aestronglyMeasurable
  have h2 : MeasureTheory.AEStronglyMeasurable
      (fun θ : ℝ => ((blgDatum c a ρ m U V u (circleMap 0 1 θ) : ℂ)))
      (MeasureTheory.volume.restrict (Set.uIoc (0:ℝ) (2 * Real.pi))) :=
    (((measurable_blgDatum hVo hUo hucont).comp
      (continuous_circleMap 0 1).measurable).complex_ofReal).aestronglyMeasurable
  have hmeas := h1.smul h2
  have hbdd : ∀ᵐ θ ∂(MeasureTheory.volume.restrict (Set.uIoc (0:ℝ) (2 * Real.pi))),
      ‖deriv (circleMap (0 : ℂ) 1) θ •
        ((blgDatum c a ρ m U V u (circleMap 0 1 θ) : ℂ))‖ ≤ 1 := by
    filter_upwards with θ
    rw [norm_smul, norm_deriv_circleMap_one, one_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (blgDatum_nonneg c a ρ m U V u _)]
    exact blgDatum_le_one c a ρ m U V u _
  rw [circleIntegrable_iff, intervalIntegrable_iff]
  exact MeasureTheory.IntegrableOn.of_bound hvol hmeas 1 hbdd


/-! ## The collar function: the Poisson integral of the datum composed with the chart -/

/-- The complex Poisson core: an analytic function whose real part is the Poisson integral. -/
noncomputable def poissonCore (g : ℂ → ℝ) : ℂ → ℂ :=
  fun w => Real.circleAverage (fun z : ℂ => herglotzRieszKernel 0 w z • (g z : ℂ)) 0 1

lemma poissonCore_analytic {g : ℂ → ℝ} (hg : CircleIntegrable (fun z : ℂ => (g z : ℂ)) 0 1) :
    AnalyticOnNhd ℂ (poissonCore g) (Metric.ball (0 : ℂ) 1) :=
  (analyticOnNhd_circleAverage_herglotzRieszKernel_smul (f := fun z : ℂ => (g z : ℂ)) (R := 1) hg).mono
      (fun w hw hs => by
        rw [Metric.mem_sphere, dist_zero_right] at hs
        rw [Metric.mem_ball, dist_zero_right] at hw
        linarith [le_abs_self (1:ℝ)])

lemma poissonCore_re {g : ℂ → ℝ} (hg : CircleIntegrable (fun z : ℂ => (g z : ℂ)) 0 1)
    {w : ℂ} (hw : w ∈ Metric.ball (0 : ℂ) 1) :
    (poissonCore g w).re = Commons.Analysis.Complex.Harmonic.poissonInt g 1 w := by
  have hgR : CircleIntegrable g 0 1 := Work.Analysis.Poisson.circleIntegrable_of_ofReal hg
  rw [poissonCore, re_circleAverage_herglotzRieszKernel_smul hgR (fun hs => by
          rw [Metric.mem_sphere, dist_zero_right] at hs
          rw [Metric.mem_ball, dist_zero_right] at hw
          linarith [le_abs_self (1:ℝ)]),
    Commons.Analysis.Complex.Harmonic.poissonInt]
  congr 1
  funext z
  simp only [Pi.smul_apply, Pi.mul_apply, smul_eq_mul, Function.comp_apply,
    poissonKernel_eq_re_herglotzRieszKernel, Pi.sub_apply, Pi.div_apply]

/-- The collar function. -/
noncomputable def collar (c : OpenPartialHomeomorph X ℂ) (a : ℂ) (ρ m : ℝ) (U V : Set X)
    (u : X → ℝ) : X → ℝ :=
  fun x => Commons.Analysis.Complex.Harmonic.poissonInt (blgDatum c a ρ m U V u) 1
    ((c x - a) / ρ)

/-- **The collar function is harmonic on the chart ball.** -/
lemma harmonicOnXAt_collar {q : X} {a : ℂ} {ρ m : ℝ} {U V : Set X} {u : X → ℝ}
    (hVo : IsOpen V) (hUo : IsOpen U) (hucont : ContinuousOn u V)
    {x : X} (hx : x ∈ Submission.chartBall (chartAt ℂ q) a ρ)
    (hxq : x ∈ (chartAt ℂ q).source) :
    Submission.HarmonicOnXAt (collar (chartAt ℂ q) a ρ m U V u) x := by
  have hg : CircleIntegrable
      (fun z : ℂ => (blgDatum (chartAt ℂ q) a ρ m U V u z : ℂ)) 0 1 :=
    circleIntegrable_blgDatum hVo hUo hucont
  set d : OpenPartialHomeomorph X ℂ := chartAt ℂ x with hd
  have hxsrc : x ∈ d.source := mem_chart_source ℂ x
  set T : ℂ → ℂ := fun v => ((chartAt ℂ q) (d.symm v) - a) / ρ with hT
  have hbsrc : d x ∈ (d.symm.trans (chartAt ℂ q)).source := by
    rw [OpenPartialHomeomorph.trans_source, Set.mem_inter_iff, Set.mem_preimage]
    refine ⟨d.map_source hxsrc, ?_⟩
    rw [d.left_inv hxsrc]
    exact hxq
  have hAna1 : AnalyticAt ℂ (fun v : ℂ => (chartAt ℂ q) (d.symm v)) (d x) :=
    (Commons.Geometry.Manifold.chart_transition_analyticOnNhd x q) (d x) hbsrc
  have hAnaT : AnalyticAt ℂ T (d x) := by
    rw [hT]
    exact AnalyticAt.div_const (AnalyticAt.sub hAna1 analyticAt_const) (c := (ρ : ℂ))
  have hTb : T (d x) = ((chartAt ℂ q) x - a) / ρ := by
    simp only [hT]
    rw [d.left_inv hxsrc]
  have hxball : ‖(chartAt ℂ q) x - a‖ < ρ := by
    have h2 := hx.2
    simpa [Metric.mem_ball, dist_eq_norm] using h2
  have hρpos : (0:ℝ) < ρ := lt_of_le_of_lt (norm_nonneg _) hxball
  have hTball : T (d x) ∈ Metric.ball (0 : ℂ) 1 := by
    rw [hTb, Metric.mem_ball, dist_zero_right, norm_div, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos hρpos, div_lt_one hρpos]
    exact hxball
  have hComp : AnalyticAt ℂ (poissonCore (blgDatum (chartAt ℂ q) a ρ m U V u) ∘ T) (d x) :=
    AnalyticAt.comp (((poissonCore_analytic hg) (T (d x))) hTball) hAnaT
  have hHarm : InnerProductSpace.HarmonicAt
      (fun v : ℂ => ((poissonCore (blgDatum (chartAt ℂ q) a ρ m U V u) ∘ T) v).re) (d x) :=
    hComp.harmonicAt_re
  have hcontT : ContinuousAt T (d x) := hAnaT.continuousAt
  have hev : ∀ᶠ v in 𝓝 (d x), T v ∈ Metric.ball (0 : ℂ) 1 :=
    hcontT.eventually (Metric.isOpen_ball.mem_nhds hTball)
  have hid : (fun v : ℂ => ((poissonCore (blgDatum (chartAt ℂ q) a ρ m U V u) ∘ T) v).re)
      =ᶠ[𝓝 (d x)] (fun v : ℂ => Commons.Analysis.Complex.Harmonic.poissonInt
        (blgDatum (chartAt ℂ q) a ρ m U V u) 1 (T v)) := by
    filter_upwards [hev] with v hv
    exact poissonCore_re hg hv
  have h1 : InnerProductSpace.HarmonicAt
      (fun v : ℂ => Commons.Analysis.Complex.Harmonic.poissonInt
        (blgDatum (chartAt ℂ q) a ρ m U V u) 1 (T v)) (d x) :=
    (InnerProductSpace.harmonicAt_congr_nhds hid).mp hHarm
  have h2 : (fun v : ℂ => Commons.Analysis.Complex.Harmonic.poissonInt
        (blgDatum (chartAt ℂ q) a ρ m U V u) 1 (T v))
      = ((collar (chartAt ℂ q) a ρ m U V u) ∘ d.symm) := rfl
  rw [h2] at h1
  exact h1


/-! ## Properties of the collar function -/

/-- The Poisson integral of a nonnegative datum is nonnegative on the disc. -/
lemma poissonInt_nonneg_of_nonneg {g : ℂ → ℝ} (hg0 : ∀ z, 0 ≤ g z) {r : ℝ} (hr : 0 < r)
    {w : ℂ} (hw : ‖w‖ < r) :
    0 ≤ Commons.Analysis.Complex.Harmonic.poissonInt g r w := by
  rw [Commons.Analysis.Complex.Harmonic.poissonInt, Real.circleAverage_def, smul_eq_mul]
  have h1 : 0 ≤ ∫ θ in (0:ℝ)..(2 * Real.pi),
      poissonKernel 0 w (circleMap 0 r θ) * g (circleMap 0 r θ) := by
    refine intervalIntegral.integral_nonneg (by positivity) (fun θ _ => ?_)
    refine mul_nonneg (Commons.Analysis.Complex.Harmonic.poissonKernel_pos_r hw ?_) (hg0 _)
    rw [norm_circleMap_zero, abs_of_pos hr]
  have h2 : (0:ℝ) ≤ (2 * Real.pi)⁻¹ := by positivity
  exact mul_nonneg h2 h1

/-- On the unit circle the Poisson kernel at the centre is `1`. -/
lemma poissonKernel_zero_zero' {z : ℂ} (hz : ‖z‖ = 1) : poissonKernel 0 0 z = 1 := by
  rw [poissonKernel_def]
  have h : ‖z - 0‖ = 1 := by simpa using hz
  rw [show (‖z - 0‖ ^ 2 - ‖(0:ℂ) - 0‖ ^ 2) = 1 by rw [h]; norm_num]
  rw [show ‖(z - 0) - ((0:ℂ) - 0)‖ = 1 by simpa using h]
  norm_num

/-- The Poisson integral of a datum over the unit circle at the centre is the circle average. -/
lemma poissonInt_apply_zero' {g : ℂ → ℝ} :
    Commons.Analysis.Complex.Harmonic.poissonInt g 1 0 = Real.circleAverage g 0 1 := by
  rw [Commons.Analysis.Complex.Harmonic.poissonInt]
  refine Real.circleAverage_congr_sphere (fun z hz => ?_)
  have hz1 : ‖z‖ = 1 := by
    have h := hz
    rw [Metric.mem_sphere, dist_zero_right, abs_of_pos (by norm_num : (0:ℝ) < 1)] at h
    exact h
  rw [poissonKernel_zero_zero' hz1, one_mul]

/-- The Poisson integral of a circle-integrable datum is harmonic on the disc. -/
lemma poissonInt_harmonicOnNhd' {g : ℂ → ℝ}
    (hg : CircleIntegrable (fun z : ℂ => (g z : ℂ)) 0 1) :
    InnerProductSpace.HarmonicOnNhd (Commons.Analysis.Complex.Harmonic.poissonInt g 1)
      (Metric.ball (0 : ℂ) 1) := by
  intro x hx
  have hG : CircleIntegrable (fun z : ℂ => (g z : ℂ)) 0 1 := hg
  let G : ℂ → ℂ := fun z => (g z : ℂ)
  have hg_int : CircleIntegrable g 0 1 := Work.Analysis.Poisson.circleIntegrable_of_ofReal hg
  let F : ℂ → ℂ := fun w => Real.circleAverage (fun z : ℂ => herglotzRieszKernel 0 w z • G z) 0 1
  have hF_analytic : AnalyticOnNhd ℂ F (Metric.ball 0 1) :=
    (analyticOnNhd_circleAverage_herglotzRieszKernel_smul (f := G) (R := 1) hG).mono
      (fun w hw hs => by
        rw [Metric.mem_sphere, dist_zero_right] at hs
        rw [Metric.mem_ball, dist_zero_right] at hw
        linarith [le_abs_self (1:ℝ)])
  have hFx : AnalyticAt ℂ F x := hF_analytic x hx
  have hRe : InnerProductSpace.HarmonicAt (fun w : ℂ => (F w).re) x := hFx.harmonicAt_re
  have h_eq : (fun w : ℂ => (F w).re) =ᶠ[𝓝 x] Commons.Analysis.Complex.Harmonic.poissonInt g 1 := by
    filter_upwards [Metric.isOpen_ball.mem_nhds hx] with w hw
    have h1 : (F w).re = Real.circleAverage ((Complex.re ∘ herglotzRieszKernel 0 w) • g) 0 1 :=
      re_circleAverage_herglotzRieszKernel_smul hg_int (fun hs => by
          rw [Metric.mem_sphere, dist_zero_right] at hs
          rw [Metric.mem_ball, dist_zero_right] at hw
          linarith [le_abs_self (1:ℝ)])
    rw [h1, Commons.Analysis.Complex.Harmonic.poissonInt]
    congr 1
    funext z
    simp only [Pi.mul_apply, Pi.smul_apply, smul_eq_mul, Function.comp_apply,
      poissonKernel_eq_re_herglotzRieszKernel]
  exact (InnerProductSpace.harmonicAt_congr_nhds h_eq.symm).mpr hRe

lemma collar_nonneg {q : X} {a : ℂ} {ρ m : ℝ} {U V : Set X} {u : X → ℝ}
    {x : X} (hx : x ∈ Submission.chartBall (chartAt ℂ q) a ρ) :
    0 ≤ collar (chartAt ℂ q) a ρ m U V u x := by
  have hg0 : ∀ z : ℂ, 0 ≤ blgDatum (chartAt ℂ q) a ρ m U V u z :=
    fun z => blgDatum_nonneg (chartAt ℂ q) a ρ m U V u z
  have h2 : ‖(chartAt ℂ q) x - a‖ < ρ := by
    have h := hx.2
    simpa [Metric.mem_ball, dist_eq_norm] using h
  have hρ : (0:ℝ) < ρ := lt_of_le_of_lt (norm_nonneg _) h2
  have hw : ‖(((chartAt ℂ q) x - a) / ρ)‖ < 1 := by
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hρ]
    exact (div_lt_one hρ).mpr h2
  exact poissonInt_nonneg_of_nonneg hg0 (by norm_num) hw

lemma collar_at_center {q : X} {a : ℂ} {ρ m : ℝ} {U V : Set X} {u : X → ℝ}
    (ha : a = (chartAt ℂ q) q) :
    collar (chartAt ℂ q) a ρ m U V u q =
      Real.circleAverage (blgDatum (chartAt ℂ q) a ρ m U V u) 0 1 := by
  rw [collar, ha, sub_self, zero_div]
  exact poissonInt_apply_zero'

/-- The collar function is continuous at the base point. -/
lemma collar_continuousAt_center {q : X} {a : ℂ} {ρ m : ℝ} {U V : Set X} {u : X → ℝ}
    (hVo : IsOpen V) (hUo : IsOpen U) (hucont : ContinuousOn u V)
    (ha : a = (chartAt ℂ q) q) (hρ : 0 < ρ) :
    ContinuousAt (collar (chartAt ℂ q) a ρ m U V u) q := by
  have hg : CircleIntegrable
      (fun z : ℂ => (blgDatum (chartAt ℂ q) a ρ m U V u z : ℂ)) 0 1 :=
    circleIntegrable_blgDatum hVo hUo hucont
  have hharm : InnerProductSpace.HarmonicOnNhd
      (Commons.Analysis.Complex.Harmonic.poissonInt
        (blgDatum (chartAt ℂ q) a ρ m U V u) 1) (Metric.ball (0:ℂ) 1) :=
    poissonInt_harmonicOnNhd' hg
  have hcont0 : Filter.Tendsto (Commons.Analysis.Complex.Harmonic.poissonInt
      (blgDatum (chartAt ℂ q) a ρ m U V u) 1) (𝓝 (0:ℂ))
      (𝓝 (Commons.Analysis.Complex.Harmonic.poissonInt
        (blgDatum (chartAt ℂ q) a ρ m U V u) 1 0)) :=
    ContinuousAt.tendsto (show ContinuousAt (Commons.Analysis.Complex.Harmonic.poissonInt
      (blgDatum (chartAt ℂ q) a ρ m U V u) 1) 0 from
        (hharm 0 (by simp)).1.continuousAt)
  have hqsrc : q ∈ (chartAt ℂ q).source := mem_chart_source ℂ q
  have hΦq : ((chartAt ℂ q) q - a) / ρ = 0 := by rw [ha, sub_self, zero_div]
  have hcontΦ : ContinuousAt (fun x : X => ((chartAt ℂ q) x - a) / ρ) q :=
    (((chartAt ℂ q).continuousAt hqsrc).sub continuousAt_const).div_const ρ
  have hcontΦ' : Filter.Tendsto (fun x : X => ((chartAt ℂ q) x - a) / ρ) (𝓝 q) (𝓝 (0:ℂ)) := by
    have h := hcontΦ.tendsto
    rwa [hΦq] at h
  have hcomp : Filter.Tendsto (fun x : X => Commons.Analysis.Complex.Harmonic.poissonInt
      (blgDatum (chartAt ℂ q) a ρ m U V u) 1 (((chartAt ℂ q) x - a) / ρ))
      (𝓝 q) (𝓝 (Commons.Analysis.Complex.Harmonic.poissonInt
        (blgDatum (chartAt ℂ q) a ρ m U V u) 1 0)) :=
    hcont0.comp hcontΦ'
  have hcollar : collar (chartAt ℂ q) a ρ m U V u = fun x : X =>
      Commons.Analysis.Complex.Harmonic.poissonInt
        (blgDatum (chartAt ℂ q) a ρ m U V u) 1 (((chartAt ℂ q) x - a) / ρ) := rfl
  show Filter.Tendsto (fun x : X => Commons.Analysis.Complex.Harmonic.poissonInt
      (blgDatum (chartAt ℂ q) a ρ m U V u) 1 (((chartAt ℂ q) x - a) / ρ))
      (𝓝 q) (𝓝 (Commons.Analysis.Complex.Harmonic.poissonInt
        (blgDatum (chartAt ℂ q) a ρ m U V u) 1 (((chartAt ℂ q) q - a) / ρ)))
  rw [hΦq]
  exact hcomp

/-! ## The chart map and the collar limit -/

lemma chartMap_mem_ball {q : X} {a : ℂ} {ρ : ℝ} (hρ : 0 < ρ) {x : X}
    (hx : x ∈ Submission.chartBall (chartAt ℂ q) a ρ) :
    ‖(((chartAt ℂ q) x - a) / ρ)‖ < 1 := by
  have h2 : ‖(chartAt ℂ q) x - a‖ < ρ := by
    have h := hx.2
    simpa [Metric.mem_ball, dist_eq_norm] using h
  rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hρ]
  exact (div_lt_one hρ).mpr h2

lemma chartMap_mem_sphere {q : X} {a : ℂ} {ρ : ℝ} (hρ : 0 < ρ) {x : X}
    (hx : x ∈ Submission.chartSphere (chartAt ℂ q) a ρ) :
    ‖(((chartAt ℂ q) x - a) / ρ)‖ = 1 := by
  have h2 : ‖(chartAt ℂ q) x - a‖ = ρ := by
    have h := hx.2
    simp only [Set.mem_preimage, Metric.mem_sphere, dist_eq_norm] at h
    exact h
  rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hρ, h2, div_self hρ.ne']

/-- On the unit circle the Poisson kernel at the centre is `1`. -/
lemma poissonKernel_zero_zero'' {z : ℂ} (hz : ‖z‖ = 1) : poissonKernel 0 0 z = 1 := by
  rw [poissonKernel_def]
  have h : ‖z - 0‖ = 1 := by simpa using hz
  rw [show ‖z - 0‖ ^ 2 - ‖(0:ℂ) - 0‖ ^ 2 = 1 by rw [h]; norm_num]
  rw [show ‖(z - 0) - ((0:ℂ) - 0)‖ = 1 by simpa using h]
  norm_num

/-- **The datum is eventually `1` near a collar point where `u < m`.** -/
lemma blgDatum_eventuallyEq_one {q : X} {a : ℂ} {ρ m : ℝ} {U V : Set X} {u : X → ℝ}
    (hρ : 0 < ρ) (htgt : Metric.closedBall a ρ ⊆ (chartAt ℂ q).target)
    (hVsub : ∀ x ∈ Submission.chartSphere (chartAt ℂ q) a ρ, x ∈ V)
    (hUo : IsOpen U) (hVo : IsOpen V) (hucont : ContinuousOn u V)
    {ξ : X} (hξU : ξ ∈ U) (hξV : ξ ∈ V)
    (hξsph : ξ ∈ Submission.chartSphere (chartAt ℂ q) a ρ) (hξm : u ξ < m) :
    ∀ᶠ z in 𝓝[Metric.sphere (0:ℂ) 1] (((chartAt ℂ q) ξ - a) / ρ),
      blgDatum (chartAt ℂ q) a ρ m U V u z = 1 := by
  have hξsrc : ξ ∈ (chartAt ℂ q).source := Submission.chartSphere_subset_source _ _ _ hξsph
  have hξeq : a + (ρ:ℂ) * (((chartAt ℂ q) ξ - a)/ρ) = (chartAt ℂ q) ξ := by
    have hρc : (ρ : ℂ) ≠ 0 := by exact_mod_cast hρ.ne'
    field_simp
    ring
  have htarget : a + (ρ : ℂ) * (((chartAt ℂ q) ξ - a) / ρ) ∈ (chartAt ℂ q).target := by
    rw [hξeq]; exact (chartAt ℂ q).map_source hξsrc
  have hψξ : badψ (chartAt ℂ q) a ρ (((chartAt ℂ q) ξ - a)/ρ) = ξ := by
    unfold badψ
    rw [hξeq]
    exact (chartAt ℂ q).left_inv hξsrc
  have hψcont : ContinuousAt (badψ (chartAt ℂ q) a ρ) (((chartAt ℂ q) ξ - a) / ρ) := by
    have h1 : ContinuousAt (fun z : ℂ => a + (ρ:ℂ) * z) (((chartAt ℂ q) ξ - a)/ρ) :=
      ContinuousAt.add continuousAt_const (ContinuousAt.mul continuousAt_const continuousAt_id)
    have h2 : ContinuousAt (chartAt ℂ q).symm (a + (ρ:ℂ) * (((chartAt ℂ q) ξ - a)/ρ)) :=
      ((chartAt ℂ q).continuousAt_symm htarget)
    exact ContinuousAt.comp (f := fun z : ℂ => a + (ρ:ℂ) * z)
      (x := (((chartAt ℂ q) ξ - a)/ρ)) h2 h1
  have hξu : ContinuousAt u (badψ (chartAt ℂ q) a ρ (((chartAt ℂ q) ξ - a)/ρ)) := by
    rw [hψξ]; exact hucont.continuousAt (hVo.mem_nhds hξV)
  have hUev : ∀ᶠ z in 𝓝 (((chartAt ℂ q) ξ - a) / ρ), badψ (chartAt ℂ q) a ρ z ∈ U :=
    hψcont.eventually (hUo.mem_nhds (by rw [hψξ]; exact hξU))
  have hVev : ∀ᶠ z in 𝓝 (((chartAt ℂ q) ξ - a) / ρ), badψ (chartAt ℂ q) a ρ z ∈ V :=
    hψcont.eventually (hVo.mem_nhds (by rw [hψξ]; exact hξV))
  have huev : ∀ᶠ z in 𝓝 (((chartAt ℂ q) ξ - a) / ρ),
      u (badψ (chartAt ℂ q) a ρ z) < m := by
    have := hξu.eventually (isOpen_Iio.mem_nhds (by rw [hψξ]; exact hξm))
    filter_upwards [hψcont.eventually this] with z hz
    simpa [Function.comp_apply] using hz
  filter_upwards [hUev.filter_mono nhdsWithin_le_nhds, hVev.filter_mono nhdsWithin_le_nhds,
    huev.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with z hzU hzV hzu hzsph
  have hz1 : ‖z‖ = 1 := by
    have h := hzsph
    rw [Metric.mem_sphere] at h
    simpa using h
  have htgtz : a + (ρ:ℂ) * z ∈ (chartAt ℂ q).target := by
    refine htgt ?_
    rw [Metric.mem_closedBall, dist_eq_norm]
    rw [show a + (ρ:ℂ)*z - a = (ρ:ℂ)*z from by ring, norm_mul, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos hρ, hz1, mul_one]
  exact blgDatum_of_mem (by
    rw [mem_blgBadSet]
    exact ⟨hz1, htgtz, ⟨hzU, hzV⟩, hzu⟩)

/-- **The collar limit at a bad collar point**: if `u ξ < m` then the collar function tends to `1`. -/
lemma collar_tendsto_one {q : X} {a : ℂ} {ρ m : ℝ} {U V : Set X} {u : X → ℝ}
    (hρ : 0 < ρ) (htgt : Metric.closedBall a ρ ⊆ (chartAt ℂ q).target)
    (hVsub : ∀ x ∈ Submission.chartSphere (chartAt ℂ q) a ρ, x ∈ V)
    (hUo : IsOpen U) (hVo : IsOpen V) (hucont : ContinuousOn u V)
    {ξ : X} (hξU : ξ ∈ U) (hξV : ξ ∈ V)
    (hξsph : ξ ∈ Submission.chartSphere (chartAt ℂ q) a ρ) (hξm : u ξ < m) :
    Filter.Tendsto (collar (chartAt ℂ q) a ρ m U V u)
      (𝓝[U ∩ Submission.chartBall (chartAt ℂ q) a ρ] ξ) (𝓝 1) := by
  have hg : CircleIntegrable
      (fun z : ℂ => (blgDatum (chartAt ℂ q) a ρ m U V u z : ℂ)) 0 1 :=
    circleIntegrable_blgDatum (V := V) (U := U) hVo hUo hucont
  have hev := blgDatum_eventuallyEq_one hρ htgt hVsub hUo hVo hucont hξU hξV hξsph hξm
  have hsphere : ‖(((chartAt ℂ q) ξ - a) / ρ)‖ = 1 := chartMap_mem_sphere hρ hξsph
  have h1 : Filter.Tendsto (fun w : ℂ => Commons.Analysis.Complex.Harmonic.poissonInt
      (blgDatum (chartAt ℂ q) a ρ m U V u) 1 w)
      (𝓝[Metric.ball (0:ℂ) 1] (((chartAt ℂ q) ξ - a) / ρ)) (𝓝 1) :=
    Work.Analysis.Poisson.poissonInt_tendsto_of_eventuallyEq (by norm_num) hg hsphere hev
  have hξsrc : ξ ∈ (chartAt ℂ q).source := Submission.chartSphere_subset_source _ _ _ hξsph
  have hcontΦ : ContinuousAt (fun x : X => ((chartAt ℂ q) x - a) / ρ) ξ :=
    (((chartAt ℂ q).continuousAt hξsrc).sub continuousAt_const).div_const ρ
  have hΦ : Filter.Tendsto (fun x : X => ((chartAt ℂ q) x - a) / ρ)
      (𝓝[U ∩ Submission.chartBall (chartAt ℂ q) a ρ] ξ)
      (𝓝[Metric.ball (0:ℂ) 1] (((chartAt ℂ q) ξ - a) / ρ)) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨hcontΦ.tendsto.mono_left nhdsWithin_le_nhds, ?_⟩
    filter_upwards [self_mem_nhdsWithin] with x hx
    simpa [Metric.mem_ball, dist_zero_right] using chartMap_mem_ball hρ hx.2
  exact h1.comp hΦ


/-! ## The measure estimate for the bad set -/

/-- The bad `θ`-set: the angles whose circle point lies in the bad set. -/
def badTheta (q : X) (a : ℂ) (ρ m : ℝ) (U V : Set X) (u : X → ℝ) : Set ℝ :=
  Set.Ioc 0 (2 * Real.pi) ∩ {θ : ℝ | circleMap 0 1 θ ∈ blgBadSet (chartAt ℂ q) a ρ m U V u}

lemma badTheta_subset (q : X) (a : ℂ) (ρ m : ℝ) (U V : Set X) (u : X → ℝ) :
    badTheta q a ρ m U V u ⊆ Set.Ioc 0 (2 * Real.pi) := fun θ hθ => hθ.1

lemma badTheta_mono (q : X) (a : ℂ) (ρ : ℝ) (U V : Set X) (u : X → ℝ) :
    Monotone fun m : ℝ => badTheta q a ρ m U V u := by
  intro m m' hmm' θ hθ
  simp only [badTheta, Set.mem_inter_iff, Set.mem_setOf_eq] at hθ ⊢
  refine ⟨hθ.1, ?_⟩
  rw [mem_blgBadSet] at hθ ⊢
  exact ⟨hθ.2.1, hθ.2.2.1, hθ.2.2.2.1, lt_of_lt_of_le hθ.2.2.2.2 hmm'⟩

lemma measurableSet_badTheta {q : X} {a : ℂ} {ρ m : ℝ} {U V : Set X} {u : X → ℝ}
    (hVo : IsOpen V) (hUo : IsOpen U) (hucont : ContinuousOn u V) :
    MeasurableSet (badTheta q a ρ m U V u) := by
  refine measurableSet_Ioc.inter ?_
  exact (measurableSet_blgBadSet hVo hUo hucont).preimage
    (continuous_circleMap 0 1).measurable
/-! ## Sums of superharmonic functions -/

theorem superharmonicOnX_add {u v : X → ℝ} {U : Set X}
    (hu : Submission.SuperharmonicOnX u U) (hv : Submission.SuperharmonicOnX v U) :
    Submission.SuperharmonicOnX (fun x => u x + v x) U := by
  have h : Submission.SubharmonicOnX (fun x => -u x + -v x) U := (hu.neg).add (hv.neg)
  have h2 : Submission.SuperharmonicOnX (fun x => -(-u x + -v x)) U := h.neg
  have hfun : (fun x : X => -(-u x + -v x)) = fun x => u x + v x := by
    funext x; ring
  rwa [hfun] at h2

/-! ## The ball-relative collar limit -/

/-- The collar tends to `1` along the *inside* of the chart ball at a collar point where `u < m`. -/
lemma collar_tendsto_one_ball {q : X} {a : ℂ} {ρ m : ℝ} {U V : Set X} {u : X → ℝ}
    (hρ : 0 < ρ) (htgt : Metric.closedBall a ρ ⊆ (chartAt ℂ q).target)
    (hVsub : ∀ x ∈ Submission.chartSphere (chartAt ℂ q) a ρ, x ∈ V)
    (hUo : IsOpen U) (hVo : IsOpen V) (hucont : ContinuousOn u V)
    {ξ : X} (hξU : ξ ∈ U) (hξV : ξ ∈ V)
    (hξsph : ξ ∈ Submission.chartSphere (chartAt ℂ q) a ρ) (hξm : u ξ < m) :
    Filter.Tendsto (collar (chartAt ℂ q) a ρ m U V u)
      (𝓝[Submission.chartBall (chartAt ℂ q) a ρ] ξ) (𝓝 1) := by
  have hg : CircleIntegrable
      (fun z : ℂ => (blgDatum (chartAt ℂ q) a ρ m U V u z : ℂ)) 0 1 :=
    circleIntegrable_blgDatum (V := V) (U := U) hVo hUo hucont
  have hev := blgDatum_eventuallyEq_one hρ htgt hVsub hUo hVo hucont hξU hξV hξsph hξm
  have hsphere : ‖(((chartAt ℂ q) ξ - a) / ρ)‖ = 1 := chartMap_mem_sphere hρ hξsph
  have h1 : Filter.Tendsto (fun w : ℂ => Commons.Analysis.Complex.Harmonic.poissonInt
      (blgDatum (chartAt ℂ q) a ρ m U V u) 1 w)
      (𝓝[Metric.ball (0:ℂ) 1] (((chartAt ℂ q) ξ - a) / ρ)) (𝓝 1) :=
    Work.Analysis.Poisson.poissonInt_tendsto_of_eventuallyEq (by norm_num) hg hsphere hev
  have hξsrc : ξ ∈ (chartAt ℂ q).source := Submission.chartSphere_subset_source _ _ _ hξsph
  have hcontΦ : ContinuousAt (fun x : X => ((chartAt ℂ q) x - a) / ρ) ξ :=
    (((chartAt ℂ q).continuousAt hξsrc).sub continuousAt_const).div_const ρ
  have hΦ : Filter.Tendsto (fun x : X => ((chartAt ℂ q) x - a) / ρ)
      (𝓝[Submission.chartBall (chartAt ℂ q) a ρ] ξ)
      (𝓝[Metric.ball (0:ℂ) 1] (((chartAt ℂ q) ξ - a) / ρ)) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨hcontΦ.tendsto.mono_left nhdsWithin_le_nhds, ?_⟩
    filter_upwards [self_mem_nhdsWithin] with x hx
    simpa [Metric.mem_ball, dist_zero_right] using chartMap_mem_ball hρ hx
  exact h1.comp hΦ

/-! ## The Bouligand barrier -/

/-- The core of the Bouligand barrier: `2u/η` plus the Poisson collar. -/
noncomputable def barrierCore (q : X) (a : ℂ) (ρ η : ℝ) (U V : Set X) (u : X → ℝ) : X → ℝ :=
  fun x => (2 / η) * u x + collar (chartAt ℂ q) a ρ η U V u x

/-- The Bouligand barrier: `min (2u/η + collar) 1` on the chart ball, the constant `1` outside. -/
noncomputable def blgBarrier (q : X) (a : ℂ) (ρ η : ℝ) (U V : Set X) (u : X → ℝ) : X → ℝ :=
  fun x => if x ∈ Submission.chartBall (chartAt ℂ q) a ρ then min (barrierCore q a ρ η U V u x) 1
    else 1

/-- The open set where the barrier is identically `1`. -/
noncomputable def barrierGoodSet (q : X) (a : ℂ) (ρ η : ℝ) (U V : Set X) (u : X → ℝ) : Set X :=
  interior {y : X | y ∈ Submission.chartBall (chartAt ℂ q) a ρ →
    1 ≤ barrierCore q a ρ η U V u y}

lemma blgBarrier_of_mem {q : X} {a : ℂ} {ρ η : ℝ} {U V : Set X} {u : X → ℝ} {x : X}
    (hx : x ∈ Submission.chartBall (chartAt ℂ q) a ρ) :
    blgBarrier q a ρ η U V u x = min (barrierCore q a ρ η U V u x) 1 := by
  rw [blgBarrier]; exact if_pos hx

lemma blgBarrier_of_not_mem {q : X} {a : ℂ} {ρ η : ℝ} {U V : Set X} {u : X → ℝ} {x : X}
    (hx : x ∉ Submission.chartBall (chartAt ℂ q) a ρ) :
    blgBarrier q a ρ η U V u x = 1 := by
  rw [blgBarrier]; exact if_neg hx

lemma mem_barrierGoodSet {q : X} {a : ℂ} {ρ η : ℝ} {U V : Set X} {u : X → ℝ} {x : X} :
    x ∈ barrierGoodSet q a ρ η U V u ↔ ∀ᶠ y in 𝓝 x,
      y ∈ Submission.chartBall (chartAt ℂ q) a ρ → 1 ≤ barrierCore q a ρ η U V u y :=
  mem_interior_iff_mem_nhds

lemma blgBarrier_eq_one_of_mem_good {q : X} {a : ℂ} {ρ η : ℝ} {U V : Set X} {u : X → ℝ}
    {x : X} (hx : x ∈ barrierGoodSet q a ρ η U V u) :
    blgBarrier q a ρ η U V u x = 1 := by
  by_cases hxB : x ∈ Submission.chartBall (chartAt ℂ q) a ρ
  · rw [blgBarrier_of_mem hxB, min_eq_right]
    exact interior_subset hx hxB
  · exact blgBarrier_of_not_mem hxB

/-! ## The barrier core is `≥ 1` near a sphere point of `U` -/

lemma barrierCore_eventually_ge_one {q : X} {a : ℂ} {ρ η : ℝ} {U V Ω : Set X} {u : X → ℝ}
    (hρ : 0 < ρ) (hη : 0 < η) (htgt : Metric.closedBall a ρ ⊆ (chartAt ℂ q).target)
    (hVsub : ∀ x ∈ Submission.chartSphere (chartAt ℂ q) a ρ, x ∈ V)
    (hUo : IsOpen U) (hVo : IsOpen V) (hucont : ContinuousOn u V)
    (hUΩ : U ⊆ Ω) (hupos : ∀ x ∈ Ω ∩ V, 0 < u x)
    {x : X} (hxU : x ∈ U) (hxsph : x ∈ Submission.chartSphere (chartAt ℂ q) a ρ) :
    ∀ᶠ y in 𝓝 x, y ∈ Submission.chartBall (chartAt ℂ q) a ρ →
      1 ≤ barrierCore q a ρ η U V u y := by
  have hxV : x ∈ V := hVsub x hxsph
  have hxpos : 0 < u x := hupos x ⟨hUΩ hxU, hxV⟩
  have huxcont : ContinuousAt u x := hucont.continuousAt (hVo.mem_nhds hxV)
  by_cases hcase : u x < η
  · -- the collar compensates for the small value of `u`
    have hlim := collar_tendsto_one_ball (q := q) (a := a) (ρ := ρ) (m := η) (U := U) (V := V)
      (u := u) hρ htgt hVsub hUo hVo hucont hxU hxV hxsph hcase
    have hδ : 0 < u x / (2 * η) := by positivity
    have hcol : ∀ᶠ y in 𝓝[Submission.chartBall (chartAt ℂ q) a ρ] x,
        1 - u x / (2 * η) < collar (chartAt ℂ q) a ρ η U V u y :=
      hlim.eventually (isOpen_Ioi.mem_nhds (by rw [Set.mem_Ioi]; linarith))
    have hcol' : ∀ᶠ y in 𝓝 x, y ∈ Submission.chartBall (chartAt ℂ q) a ρ →
        1 - u x / (2 * η) < collar (chartAt ℂ q) a ρ η U V u y :=
      eventually_nhdsWithin_iff.mp hcol
    have huev : ∀ᶠ y in 𝓝 x, u x / 2 < u y :=
      huxcont.eventually (isOpen_Ioi.mem_nhds (by rw [Set.mem_Ioi]; linarith))
    filter_upwards [hcol', huev] with y hycol hyu
    intro hyB
    have h3 : u x / η < (2 / η) * u y := by
      have hmul : (2 / η) * (u x / 2) < (2 / η) * u y :=
        mul_lt_mul_of_pos_left hyu (by positivity)
      have heq : (2 / η) * (u x / 2) = u x / η := by field_simp
      linarith
    have h4 : u x / η + (1 - u x / (2 * η)) = 1 + u x / (2 * η) := by field_simp; ring
    have h5 : 1 - u x / (2 * η) < collar (chartAt ℂ q) a ρ η U V u y := hycol hyB
    simp only [barrierCore]
    linarith
  · -- the `u` term alone already exceeds `1`
    push_neg at hcase
    have hcase' : η / 2 < u x := by linarith
    have huev : ∀ᶠ y in 𝓝 x, η / 2 < u y :=
      huxcont.eventually (isOpen_Ioi.mem_nhds hcase')
    filter_upwards [huev] with y hy
    intro hyB
    have h1 : (1 : ℝ) < (2 / η) * u y := by
      have hmul : (2 / η) * (η / 2) < (2 / η) * u y :=
        mul_lt_mul_of_pos_left hy (by positivity)
      have heq : (2 / η) * (η / 2) = 1 := by field_simp
      linarith
    have h2 : 0 ≤ collar (chartAt ℂ q) a ρ η U V u y := collar_nonneg hyB
    simp only [barrierCore]
    linarith

/-! ## Superharmonicity of the Bouligand barrier -/

lemma blgBarrier_superharmonic {q : X} {a : ℂ} {ρ η : ℝ} {U V Ω : Set X} {u : X → ℝ}
    (hρ : 0 < ρ) (hη : 0 < η) (htgt : Metric.closedBall a ρ ⊆ (chartAt ℂ q).target)
    (hVcl : Submission.chartClosedBall (chartAt ℂ q) a ρ ⊆ V)
    (hUo : IsOpen U) (hVo : IsOpen V) (hucont : ContinuousOn u V)
    (hsup : Submission.SuperharmonicOnX u (Ω ∩ V)) (hUΩ : U ⊆ Ω)
    (hgood : U ∩ Submission.chartSphere (chartAt ℂ q) a ρ ⊆ barrierGoodSet q a ρ η U V u) :
    Submission.SuperharmonicOnX (blgBarrier q a ρ η U V u) U := by
  set B : Set X := Submission.chartBall (chartAt ℂ q) a ρ with hBdef
  have hBopen : IsOpen B := Submission.chartBall_isOpen _ _ _
  have hBsrc : B ⊆ (chartAt ℂ q).source := Submission.chartBall_subset_source _ _ _
  have hBcl : B ⊆ Submission.chartClosedBall (chartAt ℂ q) a ρ :=
    Submission.chartBall_subset_chartClosedBall _ _ _
  have hsubUB : U ∩ B ⊆ Ω ∩ V := fun x hx => ⟨hUΩ hx.1, hVcl (hBcl hx.2)⟩
  have huUB : Submission.SuperharmonicOnX u (U ∩ B) :=
    Submission.SuperharmonicOnX.mono hsup hsubUB (hsup.1.mono hsubUB)
  have hmulUB : Submission.SuperharmonicOnX (fun x => (2 / η) * u x) (U ∩ B) :=
    Submission.SuperharmonicOnX.const_mul (by positivity) huUB
  have hcolUB : Submission.SuperharmonicOnX (collar (chartAt ℂ q) a ρ η U V u) (U ∩ B) := by
    refine ⟨?_, ?_⟩
    · refine continuousOn_of_forall_continuousAt (fun x hx => ?_)
      exact (harmonicOnXAt_collar (q := q) (a := a) (ρ := ρ) hVo hUo hucont hx.2
        (hBsrc hx.2)).continuousAt
    · intro x hx
      exact (harmonicOnXAt_collar (q := q) (a := a) (ρ := ρ) hVo hUo hucont hx.2
        (hBsrc hx.2)).superharmonic
  have hsumUB : Submission.SuperharmonicOnX (barrierCore q a ρ η U V u) (U ∩ B) :=
    superharmonicOnX_add hmulUB hcolUB
  have hminUB : Submission.SuperharmonicOnX
      (fun x => min (barrierCore q a ρ η U V u x) 1) (U ∩ B) :=
    Submission.SuperharmonicOnX.min hsumUB (superharmonicOnX_const_dev 1 _)
  have hβUB : Submission.SuperharmonicOnX (blgBarrier q a ρ η U V u) (U ∩ B) :=
    Work.SimplyConnected.ABS.SuperharmonicOnX.congr_of_isOpen (hUo.inter hBopen)
      (fun x hx => blgBarrier_of_mem hx.2) hminUB
  have hβUcl : Submission.SuperharmonicOnX (blgBarrier q a ρ η U V u) (U \ closure B) :=
    Work.SimplyConnected.ABS.SuperharmonicOnX.congr_of_isOpen (hUo.sdiff isClosed_closure)
      (fun x hx => blgBarrier_of_not_mem (fun h => hx.2 (subset_closure h)))
      (superharmonicOnX_const_dev 1 _)
  have hβgood : Submission.SuperharmonicOnX (blgBarrier q a ρ η U V u)
      (barrierGoodSet q a ρ η U V u) :=
    Work.SimplyConnected.ABS.SuperharmonicOnX.congr_of_isOpen isOpen_interior
      (fun x hx => blgBarrier_eq_one_of_mem_good hx) (superharmonicOnX_const_dev 1 _)
  have hcover : ∀ x ∈ U, x ∈ (U ∩ B) ∪ (U \ closure B) ∪ barrierGoodSet q a ρ η U V u := by
    intro x hxU
    by_cases hxB : x ∈ B
    · exact Or.inl (Or.inl ⟨hxU, hxB⟩)
    · by_cases hxcl : x ∈ closure B
      · have hxcb : x ∈ Submission.chartClosedBall (chartAt ℂ q) a ρ :=
          Submission.closure_chartBall_subset_chartClosedBall (c := chartAt ℂ q) htgt hxcl
        have hxcbs : x ∈ Submission.chartSphere (chartAt ℂ q) a ρ := by
          refine ⟨hxcb.1, ?_⟩
          have h1 : dist ((chartAt ℂ q) x) a ≤ ρ := Metric.mem_closedBall.mp hxcb.2
          have h2 : ¬ (dist ((chartAt ℂ q) x) a < ρ) :=
            fun h => hxB ⟨hxcb.1, Metric.mem_ball.mpr h⟩
          show dist ((chartAt ℂ q) x) a = ρ
          exact le_antisymm h1 (not_lt.mp h2)
        exact Or.inr (hgood ⟨hxU, hxcbs⟩)
      · exact Or.inl (Or.inr ⟨hxU, hxcl⟩)
  let Wv : Fin 3 → Set X := ![(U ∩ B), (U \ closure B), barrierGoodSet q a ρ η U V u]
  have hWo : ∀ i, IsOpen (Wv i) := by
    intro i
    fin_cases i
    · simpa [Wv] using (hUo.inter hBopen)
    · simpa [Wv] using (hUo.sdiff isClosed_closure)
    · exact isOpen_interior
  have hWv : ∀ i, Submission.SuperharmonicOnX (blgBarrier q a ρ η U V u) (Wv i) := by
    intro i
    fin_cases i
    · simpa [Wv] using hβUB
    · simpa [Wv] using hβUcl
    · simpa [Wv] using hβgood
  have hcov : U ⊆ ⋃ i, Wv i := by
    intro x hx
    rcases hcover x hx with h | h
    · rcases h with h | h
      · exact Set.mem_iUnion.mpr ⟨0, by simpa [Wv] using h⟩
      · exact Set.mem_iUnion.mpr ⟨1, by simpa [Wv] using h⟩
    · exact Set.mem_iUnion.mpr ⟨2, by simpa [Wv] using h⟩
  exact Work.SimplyConnected.ABS.superharmonicOnX_of_isOpen_cover_dev hWo hcov hWv

/-! ## The measure estimate: the bad sets shrink as `η → 0` -/

/-- The bad `θ`-set along the sequence `ηₙ = 1/(n+1)`. -/
def badThetaSeq (q : X) (a : ℂ) (ρ : ℝ) (U V : Set X) (u : X → ℝ) : ℕ → Set ℝ :=
  fun n => badTheta q a ρ (1 / ((n : ℝ) + 1)) U V u

lemma antitone_badThetaSeq (q : X) (a : ℂ) (ρ : ℝ) (U V : Set X) (u : X → ℝ) :
    Antitone (badThetaSeq q a ρ U V u) := by
  intro m n hmn
  have hm : (0:ℝ) < (m : ℝ) + 1 := by positivity
  have hle : (m : ℝ) + 1 ≤ (n : ℝ) + 1 := by
    exact_mod_cast Nat.add_le_add_right hmn 1
  exact badTheta_mono q a ρ U V u (one_div_le_one_div_of_le hm hle)

lemma badThetaSeq_subset (q : X) (a : ℂ) (ρ : ℝ) (U V : Set X) (u : X → ℝ) (n : ℕ) :
    badThetaSeq q a ρ U V u n ⊆ Set.Ioc (0 : ℝ) (2 * Real.pi) :=
  badTheta_subset q a ρ (1 / ((n : ℝ) + 1)) U V u

lemma measurableSet_badThetaSeq {q : X} {a : ℂ} {ρ : ℝ} {U V : Set X} {u : X → ℝ}
    (hVo : IsOpen V) (hUo : IsOpen U) (hucont : ContinuousOn u V) (n : ℕ) :
    MeasureTheory.NullMeasurableSet (badThetaSeq q a ρ U V u n) MeasureTheory.volume :=
  (measurableSet_badTheta (q := q) (a := a) (ρ := ρ) (m := 1 / ((n : ℝ) + 1)) (U := U) (V := V)
    (u := u) hVo hUo hucont).nullMeasurableSet

lemma iInter_badThetaSeq_eq_empty {q : X} {a : ℂ} {ρ : ℝ} {U V Ω : Set X} {u : X → ℝ}
    (hUΩ : U ⊆ Ω) (hupos : ∀ x ∈ Ω ∩ V, 0 < u x) :
    (⋂ n, badThetaSeq q a ρ U V u n) = (∅ : Set ℝ) := by
  refine Set.eq_empty_iff_forall_notMem.mpr (fun θ hθ => ?_)
  have key : ∀ n : ℕ, (badψ (chartAt ℂ q) a ρ (circleMap 0 1 θ) ∈ U ∩ V) ∧
      u (badψ (chartAt ℂ q) a ρ (circleMap 0 1 θ)) < 1 / ((n : ℝ) + 1) := by
    intro n
    have hn : θ ∈ badTheta q a ρ (1 / ((n : ℝ) + 1)) U V u := Set.mem_iInter.mp hθ n
    have h2 : circleMap (0:ℂ) 1 θ ∈
        blgBadSet (chartAt ℂ q) a ρ (1 / ((n : ℝ) + 1)) U V u := hn.2
    exact ⟨(mem_blgBadSet.mp h2).2.2.1, (mem_blgBadSet.mp h2).2.2.2⟩
  obtain ⟨hUV, -⟩ := key 0
  have hpos : 0 < u (badψ (chartAt ℂ q) a ρ (circleMap 0 1 θ)) :=
    hupos _ ⟨hUΩ hUV.1, hUV.2⟩
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt hpos
  exact absurd (key n).2 (not_lt.mpr hn.le)

/-- **The circle average of the datum is bounded by the measure of the bad set.** -/
lemma circleAverage_blgDatum_le {q : X} {a : ℂ} {ρ m : ℝ} {U V : Set X} {u : X → ℝ}
    (hVo : IsOpen V) (hUo : IsOpen U) (hucont : ContinuousOn u V) :
    Real.circleAverage (blgDatum (chartAt ℂ q) a ρ m U V u) 0 1 ≤
      (MeasureTheory.volume (badTheta q a ρ m U V u)).toReal / (2 * Real.pi) := by
  have hmeas : MeasurableSet (badTheta q a ρ m U V u) :=
    measurableSet_badTheta (q := q) (a := a) (ρ := ρ) (m := m) (U := U) (V := V) (u := u)
      hVo hUo hucont
  have hvol : MeasureTheory.volume (Set.uIoc (0:ℝ) (2 * Real.pi)) < ⊤ := by
    rw [Real.volume_uIoc]; exact ENNReal.ofReal_lt_top
  have hrestr : MeasureTheory.volume.restrict (Set.uIoc (0:ℝ) (2 * Real.pi))
      ≤ MeasureTheory.volume := MeasureTheory.Measure.restrict_le_self
  have hDint : IntervalIntegrable
      (fun θ : ℝ => blgDatum (chartAt ℂ q) a ρ m U V u (circleMap 0 1 θ))
      MeasureTheory.volume 0 (2 * Real.pi) := by
    rw [intervalIntegrable_iff]
    refine MeasureTheory.IntegrableOn.of_bound hvol ?_ 1 ?_
    · exact (((measurable_blgDatum hVo hUo hucont).comp
        (continuous_circleMap 0 1).measurable).aestronglyMeasurable).mono_measure hrestr
    · filter_upwards with θ
      rw [Real.norm_eq_abs, abs_of_nonneg (blgDatum_nonneg (chartAt ℂ q) a ρ m U V u _)]
      exact blgDatum_le_one (chartAt ℂ q) a ρ m U V u _
  have hIint : IntervalIntegrable
      (fun θ : ℝ => (badTheta q a ρ m U V u).indicator (fun _ => (1:ℝ)) θ)
      MeasureTheory.volume 0 (2 * Real.pi) := by
    rw [intervalIntegrable_iff]
    refine MeasureTheory.IntegrableOn.of_bound hvol ?_ 1 ?_
    · exact ((measurable_const.indicator hmeas).aestronglyMeasurable).mono_measure hrestr
    · filter_upwards with θ
      by_cases h : θ ∈ badTheta q a ρ m U V u
      · rw [Set.indicator_of_mem h]; norm_num
      · rw [Set.indicator_of_notMem h]; norm_num
  have hmono : ∫ θ in (0:ℝ)..(2 * Real.pi),
        blgDatum (chartAt ℂ q) a ρ m U V u (circleMap 0 1 θ) ≤
      ∫ θ in (0:ℝ)..(2 * Real.pi),
        (badTheta q a ρ m U V u).indicator (fun _ => (1:ℝ)) θ := by
    refine intervalIntegral.integral_mono_on_of_le_Ioo (by positivity) hDint hIint
      (fun θ hθ => ?_)
    have hθIoc : θ ∈ Set.Ioc (0:ℝ) (2 * Real.pi) := Set.Ioo_subset_Ioc_self hθ
    by_cases hc : circleMap (0:ℂ) 1 θ ∈ blgBadSet (chartAt ℂ q) a ρ m U V u
    · have hmem : θ ∈ badTheta q a ρ m U V u := ⟨hθIoc, hc⟩
      rw [blgDatum_of_mem hc, Set.indicator_of_mem (s := badTheta q a ρ m U V u) hmem]
    · have hnot : θ ∉ badTheta q a ρ m U V u := fun h => hc h.2
      have h0 : blgDatum (chartAt ℂ q) a ρ m U V u (circleMap 0 1 θ) = 0 := by
        unfold blgDatum
        rw [Set.indicator_of_notMem (s := blgBadSet (chartAt ℂ q) a ρ m U V u) hc]
      rw [h0, Set.indicator_of_notMem (s := badTheta q a ρ m U V u) hnot]
  have hIval : ∫ θ in (0:ℝ)..(2 * Real.pi),
      (badTheta q a ρ m U V u).indicator (fun _ => (1:ℝ)) θ
      = (MeasureTheory.volume (badTheta q a ρ m U V u)).toReal := by
    rw [intervalIntegral.integral_of_le (by positivity)]
    rw [← MeasureTheory.integral_indicator
      (measurableSet_Ioc : MeasurableSet (Set.Ioc (0:ℝ) (2 * Real.pi)))]
    rw [Set.indicator_indicator]
    rw [Set.inter_eq_right.mpr (badTheta_subset q a ρ m U V u)]
    rw [MeasureTheory.integral_indicator_const (1:ℝ) hmeas, smul_eq_mul, mul_one,
      MeasureTheory.Measure.real_def]
  have havg : Real.circleAverage (blgDatum (chartAt ℂ q) a ρ m U V u) 0 1 =
      (2 * Real.pi)⁻¹ * ∫ θ in (0:ℝ)..(2 * Real.pi),
        blgDatum (chartAt ℂ q) a ρ m U V u (circleMap 0 1 θ) := by
    rw [Real.circleAverage_def, smul_eq_mul]
  rw [havg]
  have hgoal : (2 * Real.pi)⁻¹ * ∫ θ in (0:ℝ)..(2 * Real.pi),
        blgDatum (chartAt ℂ q) a ρ m U V u (circleMap 0 1 θ) ≤
      (2 * Real.pi)⁻¹ * (MeasureTheory.volume (badTheta q a ρ m U V u)).toReal :=
    mul_le_mul_of_nonneg_left (hmono.trans_eq hIval) (by positivity)
  simpa [div_eq_mul_inv, mul_comm] using hgoal

lemma exists_badThetaSeq_volume_toReal_lt {q : X} {a : ℂ} {ρ : ℝ} {U V Ω : Set X} {u : X → ℝ}
    (hVo : IsOpen V) (hUo : IsOpen U) (hucont : ContinuousOn u V)
    (hUΩ : U ⊆ Ω) (hupos : ∀ x ∈ Ω ∩ V, 0 < u x)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ n : ℕ, (MeasureTheory.volume (badThetaSeq q a ρ U V u n)).toReal < 2 * Real.pi * δ := by
  have hmeas := fun n => measurableSet_badThetaSeq (q := q) (a := a) (ρ := ρ) (U := U) (V := V)
    (u := u) hVo hUo hucont n
  have hAnti := antitone_badThetaSeq q a ρ U V u
  have hvolIoc : MeasureTheory.volume (Set.Ioc (0:ℝ) (2 * Real.pi)) ≠ ⊤ := by
    rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top
  have hfin : ∃ n, MeasureTheory.volume (badThetaSeq q a ρ U V u n) ≠ ⊤ :=
    ⟨0, ne_top_of_le_ne_top hvolIoc
      (MeasureTheory.measure_mono (badThetaSeq_subset q a ρ U V u 0))⟩
  have hemp := iInter_badThetaSeq_eq_empty (q := q) (a := a) (ρ := ρ) (U := U) (V := V) (Ω := Ω)
    (u := u) hUΩ hupos
  have htend := MeasureTheory.tendsto_measure_iInter_atTop hmeas hAnti hfin
  rw [hemp, MeasureTheory.measure_empty] at htend
  have h2πδ : (0:ℝ) < 2 * Real.pi * δ := by positivity
  have hev : ∀ᶠ n in Filter.atTop,
      MeasureTheory.volume (badThetaSeq q a ρ U V u n) < ENNReal.ofReal (2 * Real.pi * δ) :=
    htend.eventually (isOpen_Iio.mem_nhds (by simpa using ENNReal.ofReal_pos.mpr h2πδ))
  obtain ⟨n, hn⟩ := Filter.eventually_atTop.mp hev
  refine ⟨n, ?_⟩
  have hne : MeasureTheory.volume (badThetaSeq q a ρ U V u n) ≠ ⊤ :=
    ne_top_of_le_ne_top hvolIoc (MeasureTheory.measure_mono (badThetaSeq_subset q a ρ U V u n))
  have hlt := (ENNReal.toReal_lt_toReal hne ENNReal.ofReal_ne_top).mpr (hn n le_rfl)
  rwa [ENNReal.toReal_ofReal h2πδ.le] at hlt

lemma exists_eta_circleAverage_lt {q : X} {a : ℂ} {ρ : ℝ} {U V Ω : Set X} {u : X → ℝ}
    (hVo : IsOpen V) (hUo : IsOpen U) (hucont : ContinuousOn u V)
    (hUΩ : U ⊆ Ω) (hupos : ∀ x ∈ Ω ∩ V, 0 < u x)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ η : ℝ, 0 < η ∧ Real.circleAverage (blgDatum (chartAt ℂ q) a ρ η U V u) 0 1 < δ := by
  obtain ⟨n, hn⟩ := exists_badThetaSeq_volume_toReal_lt (q := q) (a := a) (ρ := ρ) (U := U)
    (V := V) (Ω := Ω) (u := u) hVo hUo hucont hUΩ hupos hδ
  have hn' : (MeasureTheory.volume (badTheta q a ρ (1 / ((n : ℝ) + 1)) U V u)).toReal
      < 2 * Real.pi * δ := hn
  refine ⟨1 / ((n:ℝ) + 1), by positivity, ?_⟩
  have hb := circleAverage_blgDatum_le (q := q) (a := a) (ρ := ρ) (m := 1 / ((n:ℝ) + 1))
    (U := U) (V := V) (u := u) hVo hUo hucont
  have h2π : (0:ℝ) < 2 * Real.pi := by positivity
  have hdiv : (MeasureTheory.volume (badTheta q a ρ (1 / ((n:ℝ) + 1)) U V u)).toReal
      / (2 * Real.pi) < δ := by
    rw [div_lt_iff₀ h2π]; linarith
  linarith

/-! ## The target -/

theorem limEnvelope_indicator_far_vanishes {X : Type*} [TopologicalSpace X] [T2Space X]
    [PreconnectedSpace X] [ChartedSpace ℂ X] [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]
    {Ω U : Set X} (hΩo : IsOpen Ω) (hUo : IsOpen U) (hUΩ : U ⊆ Ω)
    (hcomp : IsCompact (closure U)) (hfrU : (frontier U).Nonempty)
    {p : X} (hp : p ∈ frontier Ω) (hpU : p ∈ closure U)
    {V : Set X} (hVo : IsOpen V) (hpV : p ∈ V)
    {u : X → ℝ} (hu : Submission.SuperharmonicOnX u (Ω ∩ V))
    (hupos : ∀ x ∈ Ω ∩ V, 0 < u x) (hucont : ContinuousOn u V) (hup : u p = 0)
    (hVK : ∀ ζ ∈ frontier U, ζ ∉ frontier Ω → ζ ∉ closure V)
    {K : Set X} (hKfr : K ⊆ frontier U) (hKcomp : IsCompact K) (hpK : p ∉ K)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ N : Set X, N ∈ nhds p ∧ ∀ x ∈ U, x ∈ N →
      Submission.limEnvelope U (Set.indicator K (fun _ => (1 : ℝ))) 1 x < ε := by
  classical
  obtain ⟨ρ, hρ, htgt, hVcl, hdisj⟩ :=
    exists_chartBall_data' (V := V) (K := K) hVo hpV hKcomp hpK
  have hVsub : ∀ x ∈ Submission.chartSphere (chartAt ℂ p) ((chartAt ℂ p) p) ρ, x ∈ V :=
    fun x hx => hVcl (Submission.chartSphere_subset_chartClosedBall _ _ _ hx)
  -- the clamp level
  obtain ⟨η, hηpos, hηsmall⟩ := exists_eta_circleAverage_lt (q := p) (a := (chartAt ℂ p) p)
    (ρ := ρ) (U := U) (V := V) (Ω := Ω) (u := u) hVo hUo hucont hUΩ hupos (δ := ε / 2)
    (by positivity)
  -- the barrier is `1` near a collar point of `U`
  have hgood : U ∩ Submission.chartSphere (chartAt ℂ p) ((chartAt ℂ p) p) ρ ⊆
      barrierGoodSet p ((chartAt ℂ p) p) ρ η U V u := by
    intro x hx
    exact mem_barrierGoodSet.mpr
      (barrierCore_eventually_ge_one (q := p) (a := (chartAt ℂ p) p) (ρ := ρ) (η := η)
        (Ω := Ω) (U := U) (V := V) (u := u) hρ hηpos htgt hVsub hUo hVo hucont hUΩ hupos
        hx.1 hx.2)
  have hβ : Submission.SuperharmonicOnX (blgBarrier p ((chartAt ℂ p) p) ρ η U V u) U :=
    blgBarrier_superharmonic (q := p) (a := (chartAt ℂ p) p) (ρ := ρ) (η := η) (Ω := Ω)
      (U := U) (V := V) (u := u) hρ hηpos htgt hVcl hUo hVo hucont hu hUΩ hgood
  have hβ0 : ∀ x ∈ U, 0 ≤ blgBarrier p ((chartAt ℂ p) p) ρ η U V u x := by
    intro x hxU
    by_cases hxB : x ∈ Submission.chartBall (chartAt ℂ p) ((chartAt ℂ p) p) ρ
    · rw [blgBarrier_of_mem hxB]
      refine le_min ?_ zero_le_one
      have hux : 0 < u x := hupos x ⟨hUΩ hxU,
        hVcl (Submission.chartBall_subset_chartClosedBall _ _ _ hxB)⟩
      have h1 : 0 < (2 / η) * u x := by positivity
      have h2 : 0 ≤ collar (chartAt ℂ p) ((chartAt ℂ p) p) ρ η U V u x := collar_nonneg hxB
      simp only [barrierCore]
      linarith
    · rw [blgBarrier_of_not_mem hxB]; norm_num
  -- the neighbourhood of `p` on which the core is `< ε`
  have hpB : p ∈ Submission.chartBall (chartAt ℂ p) ((chartAt ℂ p) p) ρ :=
    ⟨mem_chart_source ℂ p, by
      show (chartAt ℂ p) p ∈ Metric.ball ((chartAt ℂ p) p) ρ
      exact Metric.mem_ball_self hρ⟩
  have hcore_cont : ContinuousAt (barrierCore p ((chartAt ℂ p) p) ρ η U V u) p := by
    have h1 : ContinuousAt (fun x : X => (2 / η) * u x) p :=
      ContinuousAt.mul continuousAt_const (hucont.continuousAt (hVo.mem_nhds hpV))
    have h2 : ContinuousAt (collar (chartAt ℂ p) ((chartAt ℂ p) p) ρ η U V u) p :=
      collar_continuousAt_center (q := p) (a := (chartAt ℂ p) p) (ρ := ρ) (m := η) (U := U)
        (V := V) (u := u) hVo hUo hucont rfl hρ
    exact h1.add h2
  have hcorep : barrierCore p ((chartAt ℂ p) p) ρ η U V u p < ε := by
    have h1 : barrierCore p ((chartAt ℂ p) p) ρ η U V u p =
        Real.circleAverage (blgDatum (chartAt ℂ p) ((chartAt ℂ p) p) ρ η U V u) 0 1 := by
      simp only [barrierCore, hup, mul_zero, zero_add]
      exact collar_at_center (q := p) (a := (chartAt ℂ p) p) (ρ := ρ) (m := η) (U := U)
        (V := V) (u := u) rfl
    rw [h1]; linarith
  have hN : (Submission.chartBall (chartAt ℂ p) ((chartAt ℂ p) p) ρ ∩
      {x : X | barrierCore p ((chartAt ℂ p) p) ρ η U V u x < ε}) ∈ 𝓝 p :=
    Filter.inter_mem ((Submission.chartBall_isOpen _ _ _).mem_nhds hpB)
      (hcore_cont.eventually (isOpen_Iio.mem_nhds hcorep))
  -- the Perron family is nonempty
  have hneF : (Submission.limFamily U (Set.indicator K (fun _ => (1:ℝ))) 1).Nonempty := by
    refine ⟨fun _ => 0, ?_, ?_, ?_⟩
    · exact (Submission.harmonicOnX_const (0:ℝ)).subharmonic continuousOn_const
    · intro x; exact zero_le_one
    · intro ζ hζ δ hδ
      exact Filter.Eventually.of_forall (fun z => by
        have h := Set.indicator_nonneg (s := K) (f := fun _ => (1:ℝ)) (fun a ha => zero_le_one) ζ
        linarith)
  -- the barrier is continuous on `K` and `≥ 1` there
  have hKcont : ∀ ζ ∈ K, ContinuousAt (blgBarrier p ((chartAt ℂ p) p) ρ η U V u) ζ := by
    intro ζ hζ
    have hζc : ζ ∉ closure (Submission.chartBall (chartAt ℂ p) ((chartAt ℂ p) p) ρ) :=
      fun h => (Set.disjoint_left.mp hdisj h) hζ
    refine (continuousAt_const : ContinuousAt (fun _ : X => (1:ℝ)) ζ).congr ?_
    filter_upwards [isClosed_closure.isOpen_compl.mem_nhds hζc] with y hy
    exact (blgBarrier_of_not_mem (fun hyB => hy (subset_closure hyB))).symm
  have hmβ : ∀ ζ ∈ K, (1:ℝ) ≤ blgBarrier p ((chartAt ℂ p) p) ρ η U V u ζ := by
    intro ζ hζ
    have hζc : ζ ∉ Submission.chartBall (chartAt ℂ p) ((chartAt ℂ p) p) ρ :=
      fun h => (Set.disjoint_left.mp hdisj (subset_closure h)) hζ
    rw [blgBarrier_of_not_mem hζc]
  have hf : ∀ ζ ∈ frontier U, ζ ∉ K → Set.indicator K (fun _ => (1:ℝ)) ζ ≤ 0 := by
    intro ζ hζU hζK
    rw [Set.indicator_of_notMem hζK]
  have hcmp := limEnvelope_le_smul_of_barrier (M := 1) hUo hcomp hfrU (by norm_num : (0:ℝ) ≤ 1)
    hneF hβ hβ0 hKfr hKcont one_pos hmβ hf
  refine ⟨Submission.chartBall (chartAt ℂ p) ((chartAt ℂ p) p) ρ ∩
    {x : X | barrierCore p ((chartAt ℂ p) p) ρ η U V u x < ε}, hN, fun x hxU hxN => ?_⟩
  have h1 : Submission.limEnvelope U (Set.indicator K (fun _ => (1:ℝ))) 1 x ≤
      (1 / 1) * blgBarrier p ((chartAt ℂ p) p) ρ η U V u x := hcmp x hxU
  rw [one_div, inv_one, one_mul] at h1
  have h2 : blgBarrier p ((chartAt ℂ p) p) ρ η U V u x < ε := by
    rw [blgBarrier_of_mem hxN.1]
    exact lt_of_le_of_lt (min_le_left _ _) hxN.2
  linarith

end

end Work.SimplyConnected.ABS.FarLocal
