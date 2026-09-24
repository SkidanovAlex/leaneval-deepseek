import Mathlib
import Submission.Work.SimplyConnected.ABS.GreenSetupReg
import Submission.Work.SimplyConnected.ABS.circleAverageNormSq
import Submission.Commons.Analysis.Complex.Harmonic.circleMeanValue_ge_sup

/-!
# The region sweep of a chart cone

This module isolates, as a standalone sorry-free theorem, the "region sweep" step of the
globalized-barrier construction.  Let `Ω` be open, `p ∈ X`, and let

`chartCone c a ρ := x ↦ max 0 (‖c x - a‖ - ρ)`

be the *uncapped* chart cone (subharmonic, not globally bounded — capping it at a constant is
impossible, see `NOTES_globalizedBarrierGlobal_SESSION4.md`).  On the relatively compact region

`U := Ω ∩ chartBall (chartAt ℂ p) ((chartAt ℂ p) p) ρ₂`  (with `ρ < ρ₂`),

the cone is *bounded by `ρ₂ - ρ`*, so the constant `ρ₂ - ρ` is a member of the sweep family and the
sweep is available:

* `sweep G U` is **harmonic** on `U`;
* it **dominates** the cone (`G ≤ sweep G U`), hence is **strictly positive** off
  `chartClosedBall c a ρ`;
* it is **nonnegative** and **bounded by `ρ₂ - ρ`**;
* it is **dominated by every member** of the sweep family — this is the interface through which an
  upper bound near `p` (hence the vanishing of the sweep at `p`) has to be fed in, cf.
  `sweep_region_cone_lt_of_member` below.

The point of stating this separately is that `Submission.sweepFamily` imposes the domination
`G ≤ v` **only on `U`** (unlike `Submission.limFamily`, whose members are bounded by `M` on all of
`X`); this is exactly what makes the construction work in the parabolic case, where a
bounded-above subharmonic function on `X` is constant.
-/

open LeanEval.Geometry
open scoped Manifold ContDiff Topology

set_option linter.unusedSectionVars false

noncomputable section

open Filter Set Classical

namespace Work.SimplyConnected.ABS

variable {X : Type*} [TopologicalSpace X] [T2Space X] [ChartedSpace ℂ X]
  [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]

/-- The **uncapped chart cone** of radius `ρ` centred at `a`: `x ↦ max 0 (‖c x - a‖ - ρ)`. -/
noncomputable def chartCone (c : OpenPartialHomeomorph X ℂ) (a : ℂ) (ρ : ℝ) : X → ℝ :=
  fun x => max 0 (‖c x - a‖ - ρ)

/-! ## The Euclidean inputs -/

/-- **The circle average of an affine map centred at the base point vanishes.** -/
theorem circleAverage_center_sub (z : ℂ) (r : ℝ) :
    Real.circleAverage (fun w : ℂ => w - z) z r = 0 := by
  have hint : CircleIntegrable (fun w : ℂ => w - z) z r :=
    (by fun_prop : ContinuousOn (fun w : ℂ => w - z) (Metric.sphere z |r|)).circleIntegrable'
  refine Complex.ext ?_ ?_
  · change Complex.reCLM (Real.circleAverage (fun w : ℂ => w - z) z r) = Complex.reCLM (0 : ℂ)
    rw [← ContinuousLinearMap.circleAverage_comp_comm Complex.reCLM hint,
      show (⇑Complex.reCLM ∘ fun w : ℂ => w - z) = (fun w : ℂ => (w - z).re) from rfl,
      circleAverage_sub_center_re z r, map_zero]
  · change Complex.imCLM (Real.circleAverage (fun w : ℂ => w - z) z r) = Complex.imCLM (0 : ℂ)
    rw [← ContinuousLinearMap.circleAverage_comp_comm Complex.imCLM hint,
      show (⇑Complex.imCLM ∘ fun w : ℂ => w - z) = (fun w : ℂ => (w - z).im) from rfl,
      circleAverage_sub_center_im z r, map_zero]

/-- **The circle average of an affine map is its value at the centre.** -/
theorem circleAverage_sub_const (a z : ℂ) (r : ℝ) :
    Real.circleAverage (fun w : ℂ => w - a) z r = z - a := by
  have h1 : CircleIntegrable (fun w : ℂ => w - z) z r :=
    (by fun_prop : ContinuousOn (fun w : ℂ => w - z) (Metric.sphere z |r|)).circleIntegrable'
  have h2 : CircleIntegrable (fun _ : ℂ => (z - a)) z r := circleIntegrable_const (z - a) z r
  have hadd : Real.circleAverage (fun w : ℂ => (w - z) + (z - a)) z r = 0 + (z - a) := by
    rw [show (fun w : ℂ => (w - z) + (z - a))
        = (fun w : ℂ => w - z) + fun _ : ℂ => (z - a) from rfl,
      Real.circleAverage_add h1 h2, circleAverage_center_sub z r, Real.circleAverage_const]
  calc Real.circleAverage (fun w : ℂ => w - a) z r
      = Real.circleAverage (fun w : ℂ => (w - z) + (z - a)) z r := by
        congr 1
        funext w
        ring
    _ = 0 + (z - a) := hadd
    _ = z - a := by ring

/-- **The modulus is subharmonic in the circle-mean-value sense.** -/
theorem norm_sub_le_circleAverage (a z : ℂ) {r : ℝ} (hr : 0 < r) :
    ‖z - a‖ ≤ Real.circleAverage (fun w : ℂ => ‖w - a‖) z r := by
  have hint : CircleIntegrable (fun w : ℂ => w - a) z r :=
    (by fun_prop : ContinuousOn (fun w : ℂ => w - a) (Metric.sphere z |r|)).circleIntegrable'
  calc ‖z - a‖ = ‖Real.circleAverage (fun w : ℂ => w - a) z r‖ := by
        rw [circleAverage_sub_const]
    _ ≤ Real.circleAverage (fun w : ℂ => ‖w - a‖) z r := by
        rw [Real.circleAverage_def, Real.circleAverage_def, norm_smul,
          Real.norm_of_nonneg (by positivity : (0 : ℝ) ≤ (2 * Real.pi)⁻¹), smul_eq_mul]
        exact mul_le_mul_of_nonneg_left
          (intervalIntegral.norm_integral_le_integral_norm (by positivity)) (by positivity)

/-- **The clamped cone `w ↦ max 0 (‖w - a‖ - ρ)` is continuous and satisfies the circle
mean-value inequality on `ℂ`.** -/
theorem continuous_max_zero_norm_sub (a : ℂ) (ρ : ℝ) :
    Continuous (fun w : ℂ => max 0 (‖w - a‖ - ρ)) ∧
    ∀ z : ℂ, ∀ r : ℝ, 0 < r →
      max 0 (‖z - a‖ - ρ) ≤ Real.circleAverage (fun w : ℂ => max 0 (‖w - a‖ - ρ)) z r := by
  have hvcont : ContinuousOn (fun w : ℂ => ‖w - a‖ - ρ) Set.univ :=
    (((continuous_norm.comp (continuous_id.sub continuous_const)).sub
      continuous_const)).continuousOn
  have hwcont : ContinuousOn (fun _ : ℂ => (0 : ℝ)) Set.univ := continuousOn_const
  have hv : ∀ q ∈ (Set.univ : Set ℂ), ∀ r : ℝ, 0 < r →
      Metric.closedBall q r ⊆ Set.univ →
      (fun w : ℂ => ‖w - a‖ - ρ) q ≤ Real.circleAverage (fun w : ℂ => ‖w - a‖ - ρ) q r := by
    intro q _ r hr _
    have hsub := norm_sub_le_circleAverage a q hr
    have havg : Real.circleAverage (fun w : ℂ => ‖w - a‖ - ρ) q r
        = Real.circleAverage (fun w : ℂ => ‖w - a‖) q r - ρ := by
      have hi : CircleIntegrable (fun w : ℂ => ‖w - a‖) q r :=
        (by fun_prop : ContinuousOn (fun w : ℂ => ‖w - a‖) (Metric.sphere q |r|)).circleIntegrable'
      have hc : CircleIntegrable (fun _ : ℂ => ρ) q r := circleIntegrable_const ρ q r
      rw [show (fun w : ℂ => ‖w - a‖ - ρ) = (fun w : ℂ => ‖w - a‖) - fun _ : ℂ => ρ from rfl,
        Real.circleAverage_sub hi hc, Real.circleAverage_const]
    rw [havg]
    linarith
  have hw : ∀ q ∈ (Set.univ : Set ℂ), ∀ r : ℝ, 0 < r →
      Metric.closedBall q r ⊆ Set.univ →
      (fun _ : ℂ => (0 : ℝ)) q ≤ Real.circleAverage (fun _ : ℂ => (0 : ℝ)) q r := by
    intro q _ r _ _
    rw [Real.circleAverage_const]
  have hmain := Commons.Analysis.Complex.Harmonic.circleMeanValue_ge_sup isOpen_univ hvcont
    hwcont hv hw
  refine ⟨?_, fun z r hr => ?_⟩
  · rw [← continuousOn_univ]
    simpa only [max_comm] using hmain.1
  · simpa only [max_comm] using hmain.2 z trivial r hr (Set.subset_univ _)

/-! ## Subharmonicity of the cone on the chart ball -/

/-- **The chart cone is subharmonic on the chart ball.** -/
theorem subharmonicOnX_chartCone_chartBall {p : X} {ρ ρ₂ : ℝ} (hρ : 0 < ρ) (hρρ₂ : ρ < ρ₂)
    (htgt : Metric.closedBall ((chartAt ℂ p) p) ρ₂ ⊆ (chartAt ℂ p).target) :
    Submission.SubharmonicOnX
      (chartCone (chartAt ℂ p) ((chartAt ℂ p) p) ρ)
      (Submission.chartBall (chartAt ℂ p) ((chartAt ℂ p) p) ρ₂) := by
  let c : OpenPartialHomeomorph X ℂ := chartAt ℂ p
  let a : ℂ := (chartAt ℂ p) p
  have hsub₂ : Metric.closedBall a ρ₂ ⊆ c.target := htgt
  obtain ⟨hcont, hmvi⟩ := continuous_max_zero_norm_sub a ρ
  constructor
  · -- continuity on the chart ball
    have h1 : ContinuousOn (fun x : X => ‖c x - a‖ - ρ) (Submission.chartBall c a ρ₂) := by
      have h2 : ContinuousOn (fun x : X => ‖c x - a‖) (Submission.chartBall c a ρ₂) :=
        ((c.continuousOn.mono (Submission.chartBall_subset_source c a ρ₂)).sub
          (continuousOn_const (c := a))).norm
      exact h2.sub (continuousOn_const (c := ρ))
    have h3 : ContinuousOn (fun x : X => max 0 (‖c x - a‖ - ρ)) (Submission.chartBall c a ρ₂) :=
      (continuousOn_const (c := (0 : ℝ))).sup h1
    exact h3
  · intro x hx
    have hxsrc : x ∈ c.source := Submission.chartBall_subset_source c a ρ₂ hx
    have hxlt : ‖c x - a‖ < ρ₂ := by
      have h2 := (Submission.mem_chartBall.mp hx).2
      rwa [Metric.mem_ball, dist_eq_norm] at h2
    have hchart : Submission.SubharmonicAtChart (chartCone c a ρ) c x := by
      refine ⟨hxsrc, (ρ₂ - ‖c x - a‖) / 2, by linarith, ?_, ?_, ?_⟩
      · -- the smaller ball stays in the target
        intro w hw
        have hw' : ‖w - c x‖ < (ρ₂ - ‖c x - a‖) / 2 := by
          rwa [Metric.mem_ball, dist_eq_norm] at hw
        have h1 : ‖w - a‖ ≤ ‖w - c x‖ + ‖c x - a‖ := by
          rw [show w - a = (w - c x) + (c x - a) by ring]
          exact norm_add_le _ _
        exact hsub₂ (by
          simp only [Metric.mem_closedBall, dist_eq_norm]
          linarith)
      · -- continuity of the pullback
        refine hcont.continuousOn.congr ?_
        intro w hw
        have hw' : ‖w - c x‖ < (ρ₂ - ‖c x - a‖) / 2 := by
          rwa [Metric.mem_ball, dist_eq_norm] at hw
        have h1 : ‖w - a‖ ≤ ‖w - c x‖ + ‖c x - a‖ := by
          rw [show w - a = (w - c x) + (c x - a) by ring]
          exact norm_add_le _ _
        have hwtgt : w ∈ c.target := hsub₂ (by
          simp only [Metric.mem_closedBall, dist_eq_norm]
          linarith)
        show chartCone c a ρ (c.symm w) = max 0 (‖w - a‖ - ρ)
        rw [chartCone, c.right_inv hwtgt]
      · -- the mean-value inequality
        intro q hq r hr hqr
        have hq' : ‖q - c x‖ < (ρ₂ - ‖c x - a‖) / 2 := by
          rwa [Metric.mem_ball, dist_eq_norm] at hq
        have htq : ‖q - a‖ ≤ ‖q - c x‖ + ‖c x - a‖ := by
          rw [show q - a = (q - c x) + (c x - a) by ring]
          exact norm_add_le _ _
        have hqtgt : q ∈ c.target := hsub₂ (by
          simp only [Metric.mem_closedBall, dist_eq_norm]
          linarith)
        have hball : ∀ w ∈ Metric.closedBall q r, w ∈ c.target := by
          intro w hw
          have hw' : ‖w - c x‖ < (ρ₂ - ‖c x - a‖) / 2 := by
            have := hqr hw
            rwa [Metric.mem_ball, dist_eq_norm] at this
          have h1 : ‖w - a‖ ≤ ‖w - c x‖ + ‖c x - a‖ := by
            rw [show w - a = (w - c x) + (c x - a) by ring]
            exact norm_add_le _ _
          exact hsub₂ (by
            simp only [Metric.mem_closedBall, dist_eq_norm]
            linarith)
        have hsphere : Set.EqOn ((chartCone c a ρ) ∘ c.symm)
            (fun w : ℂ => max 0 (‖w - a‖ - ρ)) (Metric.sphere q |r|) := by
          intro w hw
          have hwtgt : w ∈ c.target :=
            hball w (Metric.sphere_subset_closedBall (by simpa only [abs_of_pos hr] using hw))
          show chartCone c a ρ (c.symm w) = max 0 (‖w - a‖ - ρ)
          rw [chartCone, c.right_inv hwtgt]
        have hval : (chartCone c a ρ) (c.symm q) = max 0 (‖q - a‖ - ρ) := by
          rw [chartCone, c.right_inv hqtgt]
        show chartCone c a ρ (c.symm q) ≤
          Real.circleAverage (chartCone c a ρ ∘ c.symm) q r
        rw [hval, Real.circleAverage_congr_sphere hsphere]
        exact hmvi q r hr
    exact (Submission.SubharmonicAtChart_iff_chartAt (u := chartCone c a ρ) (a := x) (b := p)
      (by exact hxsrc)).mpr hchart



/-! ## The region sweep -/

/-- **The region sweep of the chart cone.**  On `U = Ω ∩ chartBall c a ρ₂` the sweep of the
chart cone is harmonic, dominates the cone, is nonnegative and bounded by `ρ₂ - ρ`, is strictly
positive off the closed chart ball of radius `ρ`, and is dominated by every member of the sweep
family. -/
theorem sweep_region_cone {Ω : Set X} (hΩo : IsOpen Ω) {p : X} {ρ ρ₂ : ℝ} (hρ : 0 < ρ)
    (hρρ₂ : ρ < ρ₂)
    (htgt : Metric.closedBall ((chartAt ℂ p) p) ρ₂ ⊆ (chartAt ℂ p).target) :
    Submission.HarmonicOnX
        (Submission.sweep (chartCone (chartAt ℂ p) ((chartAt ℂ p) p) ρ)
          (Ω ∩ Submission.chartBall (chartAt ℂ p) ((chartAt ℂ p) p) ρ₂))
        (Ω ∩ Submission.chartBall (chartAt ℂ p) ((chartAt ℂ p) p) ρ₂) ∧
      (∀ x ∈ Ω ∩ Submission.chartBall (chartAt ℂ p) ((chartAt ℂ p) p) ρ₂,
        chartCone (chartAt ℂ p) ((chartAt ℂ p) p) ρ x ≤
          Submission.sweep (chartCone (chartAt ℂ p) ((chartAt ℂ p) p) ρ)
            (Ω ∩ Submission.chartBall (chartAt ℂ p) ((chartAt ℂ p) p) ρ₂) x) ∧
      (∀ x ∈ Ω ∩ Submission.chartBall (chartAt ℂ p) ((chartAt ℂ p) p) ρ₂,
        0 ≤ Submission.sweep (chartCone (chartAt ℂ p) ((chartAt ℂ p) p) ρ)
          (Ω ∩ Submission.chartBall (chartAt ℂ p) ((chartAt ℂ p) p) ρ₂) x) ∧
      (∀ x ∈ Ω ∩ Submission.chartBall (chartAt ℂ p) ((chartAt ℂ p) p) ρ₂,
        Submission.sweep (chartCone (chartAt ℂ p) ((chartAt ℂ p) p) ρ)
          (Ω ∩ Submission.chartBall (chartAt ℂ p) ((chartAt ℂ p) p) ρ₂) x ≤ ρ₂ - ρ) ∧
      (∀ x ∈ Ω ∩ Submission.chartBall (chartAt ℂ p) ((chartAt ℂ p) p) ρ₂,
        x ∉ Submission.chartClosedBall (chartAt ℂ p) ((chartAt ℂ p) p) ρ →
        0 < Submission.sweep (chartCone (chartAt ℂ p) ((chartAt ℂ p) p) ρ)
          (Ω ∩ Submission.chartBall (chartAt ℂ p) ((chartAt ℂ p) p) ρ₂) x) ∧
      (∀ v : X → ℝ,
        v ∈ Submission.sweepFamily (chartCone (chartAt ℂ p) ((chartAt ℂ p) p) ρ)
          (Ω ∩ Submission.chartBall (chartAt ℂ p) ((chartAt ℂ p) p) ρ₂) →
        ∀ x ∈ Ω ∩ Submission.chartBall (chartAt ℂ p) ((chartAt ℂ p) p) ρ₂,
          Submission.sweep (chartCone (chartAt ℂ p) ((chartAt ℂ p) p) ρ)
            (Ω ∩ Submission.chartBall (chartAt ℂ p) ((chartAt ℂ p) p) ρ₂) x ≤ v x) := by
  let c : OpenPartialHomeomorph X ℂ := chartAt ℂ p
  let a : ℂ := (chartAt ℂ p) p
  have hsub₂ : Metric.closedBall a ρ₂ ⊆ c.target := htgt
  have hUo : IsOpen (Ω ∩ Submission.chartBall c a ρ₂) :=
    hΩo.inter (Submission.chartBall_isOpen c a ρ₂)
  have hsub : Submission.SubharmonicOnX (chartCone c a ρ) (Ω ∩ Submission.chartBall c a ρ₂) := by
    have h0 := subharmonicOnX_chartCone_chartBall (p := p) hρ hρρ₂ htgt
    exact h0.mono Set.inter_subset_right (h0.1.mono Set.inter_subset_right)
  have hmem : (fun _ : X => ρ₂ - ρ) ∈ Submission.sweepFamily (chartCone c a ρ)
      (Ω ∩ Submission.chartBall c a ρ₂) := by
    refine ⟨⟨continuousOn_const, fun x _ => ?_⟩, fun x hx => ?_⟩
    · exact (Submission.harmonicOnXAt_const (ρ₂ - ρ)).superharmonic
    · have hxlt : ‖c x - a‖ < ρ₂ := by
        have h2 := (Submission.mem_chartBall.mp hx.2).2
        rwa [Metric.mem_ball, dist_eq_norm] at h2
      show chartCone c a ρ x ≤ ρ₂ - ρ
      rw [chartCone]
      exact max_le (by linarith) (by linarith)
  have hne : (Submission.sweepFamily (chartCone c a ρ)
      (Ω ∩ Submission.chartBall c a ρ₂)).Nonempty := ⟨_, hmem⟩
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ :
      Submission.HarmonicOnX (Submission.sweep (chartCone c a ρ)
          (Ω ∩ Submission.chartBall c a ρ₂)) (Ω ∩ Submission.chartBall c a ρ₂) ∧
        (∀ x ∈ Ω ∩ Submission.chartBall c a ρ₂, chartCone c a ρ x ≤
          Submission.sweep (chartCone c a ρ) (Ω ∩ Submission.chartBall c a ρ₂) x) ∧
        (∀ x ∈ Ω ∩ Submission.chartBall c a ρ₂, 0 ≤
          Submission.sweep (chartCone c a ρ) (Ω ∩ Submission.chartBall c a ρ₂) x) ∧
        (∀ x ∈ Ω ∩ Submission.chartBall c a ρ₂,
          Submission.sweep (chartCone c a ρ) (Ω ∩ Submission.chartBall c a ρ₂) x ≤ ρ₂ - ρ) ∧
        (∀ x ∈ Ω ∩ Submission.chartBall c a ρ₂, x ∉ Submission.chartClosedBall c a ρ →
          0 < Submission.sweep (chartCone c a ρ) (Ω ∩ Submission.chartBall c a ρ₂) x) ∧
        (∀ v : X → ℝ, v ∈ Submission.sweepFamily (chartCone c a ρ)
            (Ω ∩ Submission.chartBall c a ρ₂) →
          ∀ x ∈ Ω ∩ Submission.chartBall c a ρ₂,
            Submission.sweep (chartCone c a ρ) (Ω ∩ Submission.chartBall c a ρ₂) x ≤ v x) :=
    ⟨Submission.sweep_harmonic hUo hsub hne,
      fun x hx => Submission.barrier_le_sweep hne hx,
      fun x hx => Submission.sweep_nonneg hne (fun y _ => by
        show 0 ≤ chartCone c a ρ y
        rw [chartCone]; exact le_max_left _ _) hx,
      fun x hx => Submission.sweep_le_of_mem hmem hx,
      fun x hx hxnot => by
        have hxsrc : x ∈ c.source := (Submission.mem_chartBall.mp hx.2).1
        have hgt : ρ < ‖c x - a‖ := by
          by_contra hcon
          refine hxnot (Submission.mem_chartClosedBall.mpr ⟨hxsrc, ?_⟩)
          have hle' : ‖c x - a‖ ≤ ρ := not_lt.mp hcon
          simpa [Metric.mem_closedBall, dist_eq_norm] using hle'
        have hGx : 0 < chartCone c a ρ x := by
          show 0 < max 0 (‖c x - a‖ - ρ)
          exact lt_max_iff.mpr (Or.inr (by linarith))
        exact lt_of_lt_of_le hGx (Submission.barrier_le_sweep hne hx),
      fun v hv x hx => Submission.sweep_le_of_mem hv hx⟩
  exact ⟨h1, h2, h3, h4, h5, h6⟩

/-- **Vanishing at `p` for the region sweep.**  If some member `v` of the sweep family is `< ε` on a
neighbourhood of `p` (inside `U`), then so is the sweep. -/
theorem sweep_region_cone_lt_of_member {Ω : Set X} {p : X} {ρ ρ₂ : ℝ} (hρ : 0 < ρ)
    {v : X → ℝ}
    (hv : v ∈ Submission.sweepFamily (chartCone (chartAt ℂ p) ((chartAt ℂ p) p) ρ)
      (Ω ∩ Submission.chartBall (chartAt ℂ p) ((chartAt ℂ p) p) ρ₂))
    (hv0 : ∀ ε : ℝ, 0 < ε → ∃ N : Set X, N ∈ 𝓝 p ∧
      ∀ x ∈ Ω ∩ Submission.chartBall (chartAt ℂ p) ((chartAt ℂ p) p) ρ₂ ∩ N, v x < ε) :
    ∀ ε : ℝ, 0 < ε → ∃ N : Set X, N ∈ 𝓝 p ∧
      ∀ x ∈ Ω ∩ Submission.chartBall (chartAt ℂ p) ((chartAt ℂ p) p) ρ₂ ∩ N,
        Submission.sweep (chartCone (chartAt ℂ p) ((chartAt ℂ p) p) ρ)
          (Ω ∩ Submission.chartBall (chartAt ℂ p) ((chartAt ℂ p) p) ρ₂) x < ε := by
  intro ε hε
  obtain ⟨N, hN, hNv⟩ := hv0 ε hε
  exact ⟨N, hN, fun x hx =>
    lt_of_le_of_lt (Submission.sweep_le_of_mem hv hx.1) (hNv x hx)⟩

end Work.SimplyConnected.ABS
