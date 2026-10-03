import Mathlib
import Submission.Lib.Unif2.Work.Kernel.GreenCover
import Submission.Lib.Unif2.Work.Kernel.exists_modelBump_chartBall
import Submission.Lib.Unif2.Work.Drive.chartPoleIdentity
import Submission.Lib.Unif2.Work.Drive.energyGreenRung
import Submission.Lib.Unif2.Work.SimplyConnected.ABS.manifold_smooth_upgrade
import Submission.Lib.Unif2.Work.Analysis.integrable_inv_norm_mul
import Submission.Lib.Unif2.Work.Analysis.Harmonic.integrable_inner_gradient_logNorm_sub
import Submission.Lib.Unif2.Work.Analysis.Harmonic.integrable_inner_gradient_of_contDiffAt_near

/-!
# Tools for `Work.Kernel.pairing_pole_smooth`

This module collects the self-contained analytic tools used by the discharge of the certificates of
`Work.Kernel.pairing_pole_kernel_general`:

* `contDiffAt_chart_of_contMDiff'` : a real-smooth function on the manifold has `C¹` chart
  representatives in every chart of the atlas.
* `gradient_clampedPullback_le'` : the gradient of a clamped chart pullback is bounded on a strictly
  smaller closed ball (only the chart-wise `C¹` property of the function is needed).
* `aeStronglyMeasurable_gradient_clampedPullback'` : the gradient of a clamped chart pullback is
  almost everywhere strongly measurable, the only points where the chart representative may fail to
  be `C¹` being a single prescribed point (and the sphere of the clamping ball).
* `pairIntegrable_of_support_growth'` : the `PairIntegrable` certificate from growth bounds that are
  required only on the support of the weight (this is the form in which the pole expansion of a
  Green function gives them).
* `integrable_inner_gradient_of_growth'` : the planar integrability of `⟪∇f, ∇χ⟫` when `χ` is `C¹`
  with compact support and `∇f` grows at most like the inverse distance to a point.
-/

open Set Metric MeasureTheory Filter
open scoped Manifold Topology ContDiff Gradient

noncomputable section

set_option linter.unusedSectionVars false

namespace Work.Kernel.PS

variable {X : Type*} [TopologicalSpace X] [T2Space X] [ChartedSpace ℂ X]

/-! ## 1. Chart representatives of smooth functions -/

/-- A real-smooth function on the manifold has a `C¹` chart representative in every chart of the
atlas. -/
theorem contDiffAt_chart_of_contMDiff' {f : X → ℝ}
    [IsManifold (modelWithCornersSelf ℝ ℂ) (⊤ : WithTop ℕ∞) X]
    (hf : ContMDiff (modelWithCornersSelf ℝ ℂ) (modelWithCornersSelf ℝ ℝ)
      (((⊤ : ℕ∞) : WithTop ℕ∞)) f) (y : X) :
    ∀ x ∈ (chartAt ℂ y).source,
      ContDiffAt ℝ 1 (f ∘ (chartAt ℂ y).symm) ((chartAt ℂ y) x) := by
  intro x hx
  have hI : IsManifold (modelWithCornersSelf ℝ ℂ) (((⊤ : ℕ∞) : WithTop ℕ∞)) X := inferInstance
  have hG : HasGroupoid X
      (contDiffGroupoid (((⊤ : ℕ∞) : WithTop ℕ∞)) (modelWithCornersSelf ℝ ℂ)) := inferInstance
  have hcmax : chartAt ℂ y ∈ IsManifold.maximalAtlas (modelWithCornersSelf ℝ ℂ)
      (((⊤ : ℕ∞) : WithTop ℕ∞)) X := by
    intro e' he'
    exact ⟨hG.compatible (chart_mem_atlas ℂ y) he', hG.compatible he' (chart_mem_atlas ℂ y)⟩
  have hwit := (contMDiffWithinAt_iff_source_of_mem_maximalAtlas (I := modelWithCornersSelf ℝ ℂ)
      (n := ((⊤ : ℕ∞) : WithTop ℕ∞)) (s := Set.univ) hcmax hx).mp
      ((hf.contMDiffAt (x := x)).contMDiffWithinAt)
  simp only [show ((modelWithCornersSelf ℝ ℂ : ModelWithCorners ℝ ℂ ℂ) : ℂ → ℂ) = id from rfl,
    show (((modelWithCornersSelf ℝ ℂ : ModelWithCorners ℝ ℂ ℂ).symm : ℂ → ℂ)) = id from rfl,
    OpenPartialHomeomorph.extend_coe, OpenPartialHomeomorph.extend_coe_symm, Function.comp_apply,
    Function.comp_id, Set.range_id, Set.inter_univ, Set.preimage_univ] at hwit
  rw [contMDiffWithinAt_univ] at hwit
  exact (hwit.contDiffAt).of_le (by norm_num)

/-! ## 2. Boundedness of the gradient of a clamped chart pullback -/

/-- The gradient of a clamped pullback is bounded on the closed ball of a radius `σ < ρ`, as soon as
the chart representative of the function is `C¹` at every point of the chart source. -/
theorem gradient_clampedPullback_le' {y : X} {ρ σ : ℝ} {Φ : X → ℝ} (hσρ : σ < ρ)
    (htgt : Metric.ball ((chartAt ℂ y) y) ρ ⊆ (chartAt ℂ y).target)
    (hΦ : ∀ x ∈ (chartAt ℂ y).source,
      ContDiffAt ℝ 1 (Φ ∘ (chartAt ℂ y).symm) ((chartAt ℂ y) x)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z ∈ Metric.ball ((chartAt ℂ y) y) σ,
      ‖gradient (Work.Drive.clampedPullback y ρ Φ) z‖ ≤ C := by
  have hA : ContinuousOn (fun z : ℂ => gradient (fun w : ℂ => Φ ((chartAt ℂ y).symm w)) z)
      (Metric.closedBall ((chartAt ℂ y) y) σ) := by
    intro z hz
    have hzρ : z ∈ Metric.ball ((chartAt ℂ y) y) ρ :=
      lt_of_le_of_lt (Metric.mem_closedBall.mp hz) hσρ
    have hzsrc : (chartAt ℂ y).symm z ∈ (chartAt ℂ y).source :=
      (chartAt ℂ y).map_target (htgt hzρ)
    have hright : (chartAt ℂ y) ((chartAt ℂ y).symm z) = z :=
      (chartAt ℂ y).right_inv (htgt hzρ)
    have hF : ContDiffAt ℝ 1 (fun w : ℂ => Φ ((chartAt ℂ y).symm w)) z := by
      have h := hΦ ((chartAt ℂ y).symm z) hzsrc
      rwa [hright] at h
    have h1 : ContinuousAt
        (fun w : ℂ => fderiv ℝ (fun u : ℂ => Φ ((chartAt ℂ y).symm u)) w) z :=
      hF.continuousAt_fderiv (by norm_num)
    have h2 : ContinuousAt (fun w : ℂ => gradient (fun u : ℂ => Φ ((chartAt ℂ y).symm u)) w) z := by
      simpa only [gradient, Function.comp_def] using
        (InnerProductSpace.toDual ℝ ℂ).symm.continuous.continuousAt.comp h1
    exact h2.continuousWithinAt
  have hB : ∀ z ∈ Metric.closedBall ((chartAt ℂ y) y) σ,
      gradient (Work.Drive.clampedPullback y ρ Φ) z
        = gradient (fun w : ℂ => Φ ((chartAt ℂ y).symm w)) z := by
    intro z hz
    refine Filter.EventuallyEq.gradient_eq ?_
    filter_upwards [Metric.isOpen_ball.mem_nhds
      (lt_of_le_of_lt (Metric.mem_closedBall.mp hz) hσρ)] with w hw
    rw [Work.Drive.clampedPullback_apply_of_mem hw]
  have hcont : ContinuousOn (fun z : ℂ => gradient (Work.Drive.clampedPullback y ρ Φ) z)
      (Metric.closedBall ((chartAt ℂ y) y) σ) := hA.congr hB
  obtain ⟨C, hC⟩ := (isCompact_closedBall ((chartAt ℂ y) y) σ).exists_bound_of_continuousOn hcont
  exact ⟨max C 0, le_max_right _ _, fun z hz =>
    le_trans (hC z (Metric.ball_subset_closedBall hz)) (le_max_left _ _)⟩

/-! ## 3. Almost-everywhere strong measurability of the gradient of a clamped pullback -/

/-- The gradient of a clamped chart pullback is almost everywhere strongly measurable, provided the
chart representative of the function is `C¹` on the chart ball except possibly at a single point
`x₀` (e.g. the pole of a Green function). -/
theorem aeStronglyMeasurable_gradient_clampedPullback' {y : X} {ρ : ℝ} {u : X → ℝ} {x₀ : X}
    (htgt : Metric.ball ((chartAt ℂ y) y) ρ ⊆ (chartAt ℂ y).target)
    (hu : ∀ x ∈ Submission.chartBall (chartAt ℂ y) ((chartAt ℂ y) y) ρ, x ≠ x₀ →
      ContDiffAt ℝ 1 (u ∘ (chartAt ℂ y).symm) ((chartAt ℂ y) x)) :
    AEStronglyMeasurable (fun z : ℂ => gradient (Work.Drive.clampedPullback y ρ u) z) volume := by
  set c := chartAt ℂ y with hc
  set f : ℂ → ℂ := fun z => gradient (Work.Drive.clampedPullback y ρ u) z with hf
  set N : Set ℂ := Metric.sphere (c y) ρ ∪ {c x₀} with hN
  have hNnull : volume N = 0 := by
    rw [hN]
    exact MeasureTheory.measure_union_null
      (MeasureTheory.Measure.addHaar_sphere volume (c y) ρ) (measure_singleton (c x₀))
  have hNmeas : MeasurableSet Nᶜ :=
    ((isClosed_sphere.union isClosed_singleton).isOpen_compl).measurableSet
  have hUcont : ContinuousOn f Nᶜ := by
    intro z hz
    have hzc : z ≠ c x₀ := fun h => hz (by rw [hN]; exact Or.inr h)
    have hzns : z ∉ Metric.sphere (c y) ρ := fun h => hz (by rw [hN]; exact Or.inl h)
    by_cases hzb : z ∈ Metric.ball (c y) ρ
    · have hzright : c (c.symm z) = z := c.right_inv (htgt hzb)
      have hxball : c.symm z ∈ Submission.chartBall c (c y) ρ :=
        ⟨c.map_target (htgt hzb), by rw [Set.mem_preimage, hzright]; exact hzb⟩
      have hxne : c.symm z ≠ x₀ := by
        intro h
        exact hzc (by rw [← h, hzright])
      have hC1 : ContDiffAt ℝ 1 (fun w : ℂ => u (c.symm w)) z := by
        have h := hu (c.symm z) hxball hxne
        rwa [hzright] at h
      have heq : Work.Drive.clampedPullback y ρ u =ᶠ[𝓝 z] (fun w : ℂ => u (c.symm w)) := by
        filter_upwards [Metric.isOpen_ball.mem_nhds hzb] with w hw
        rw [Work.Drive.clampedPullback_apply_of_mem hw]
      have hC1' : ContDiffAt ℝ 1 (Work.Drive.clampedPullback y ρ u) z :=
        hC1.congr_of_eventuallyEq heq
      have h1 : ContinuousAt (fun w : ℂ => fderiv ℝ (Work.Drive.clampedPullback y ρ u) w) z :=
        hC1'.continuousAt_fderiv (by norm_num)
      have h2 : ContinuousAt f z := by
        simp only [hf]
        simpa only [gradient, Function.comp_def] using
          (InnerProductSpace.toDual ℝ ℂ).symm.continuous.continuousAt.comp h1
      exact h2.continuousWithinAt
    · by_cases hzc2 : z ∈ Metric.closedBall (c y) ρ
      · have hsp : z ∈ Metric.sphere (c y) ρ := by
          rw [Metric.mem_sphere]
          exact le_antisymm (Metric.mem_closedBall.mp hzc2) (not_lt.mp hzb)
        exact absurd hsp hzns
      · have hev2 : f =ᶠ[𝓝 z] (fun _ : ℂ => (0 : ℂ)) := by
          filter_upwards [(Metric.isClosed_closedBall.isOpen_compl).mem_nhds hzc2] with w hw
          show gradient (Work.Drive.clampedPullback y ρ u) w = 0
          have hz0 : Work.Drive.clampedPullback y ρ u =ᶠ[𝓝 w] (fun _ : ℂ => (0 : ℝ)) := by
            filter_upwards [(Metric.isClosed_closedBall.isOpen_compl).mem_nhds hw] with v hv
            exact Work.Drive.clampedPullback_eq_zero_of_notMem_ball
              (fun h => hv (Metric.ball_subset_closedBall h))
          rw [Filter.EventuallyEq.gradient_eq hz0]
          simp [gradient]
        exact (ContinuousAt.congr_of_eventuallyEq continuousAt_const hev2).continuousWithinAt
  have h1 : AEStronglyMeasurable f (volume.restrict Nᶜ) := hUcont.aestronglyMeasurable hNmeas
  have h2 : AEStronglyMeasurable f (volume.restrict N) := by
    rw [MeasureTheory.Measure.restrict_eq_zero.mpr hNnull]
    exact aestronglyMeasurable_zero_measure f
  have h3 : AEStronglyMeasurable f (volume.restrict (Nᶜ ∪ N)) :=
    aestronglyMeasurable_union_iff.mpr ⟨h1, h2⟩
  rwa [Set.compl_union_self, MeasureTheory.Measure.restrict_univ] at h3


/-! ## 4. Growth bounds for the gradient of the clamped pullback of a Green function -/

section GrowthBounds

variable [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]

/-- The clamped pullback of a Green function coincides with the honest chart pullback near every
point of the open clamping ball. -/
theorem clamped_eq_unclamped_of_mem_ball {y : X} {ρ : ℝ} {g : X → ℝ} {z : ℂ}
    (hz : z ∈ Metric.ball ((chartAt ℂ y) y) ρ) :
    (fun w : ℂ => gradient (Work.Drive.clampedPullback y ρ g) w)
      =ᶠ[𝓝 z] (fun w : ℂ => gradient (fun u : ℂ => g ((chartAt ℂ y).symm u)) w) := by
  filter_upwards [Metric.isOpen_ball.mem_nhds hz] with w hw
  exact Filter.EventuallyEq.gradient_eq (by
    filter_upwards [Metric.isOpen_ball.mem_nhds hw] with v hv
    rw [Work.Drive.clampedPullback_apply_of_mem hv])

/-- **Growth bound for the clamped chart pullback of a Green function, at the pole.**

If the chart representative of `gA` has the logarithmic expansion `-log‖·-p‖ + H` around the pole
`p = c a`, then the gradient of the clamped pullback is bounded by `C/‖z - p‖` on any closed ball
strictly inside the clamping ball. -/
theorem exists_growth_clampedPullback_le_of_logExpansion {Ω : Set X} {a : X} {gA : X → ℝ}
    {y : X} {ρ σ δ : ℝ} {H : ℂ → ℝ}
    (hgA : Work.SimplyConnected.ABS.IsGreenOn Ω a gA)
    (hσρ : σ < ρ)
    (htgt : Metric.ball ((chartAt ℂ y) y) ρ ⊆ (chartAt ℂ y).target)
    (hballΩ : Submission.chartBall (chartAt ℂ y) ((chartAt ℂ y) y) ρ ⊆ Ω)
    (hδ : 0 < δ)
    (hH : InnerProductSpace.HarmonicOnNhd H (Metric.ball ((chartAt ℂ y) a) δ))
    (hueq : ∀ z ∈ Metric.ball ((chartAt ℂ y) a) δ, z ≠ (chartAt ℂ y) a →
      gA ((chartAt ℂ y).symm z) = -Real.log ‖z - (chartAt ℂ y) a‖ + H z) :
    ∃ C : ℝ, 0 < C ∧ ∀ z ∈ Metric.closedBall ((chartAt ℂ y) y) σ,
      z ≠ (chartAt ℂ y) a →
      ‖gradient (Work.Drive.clampedPullback y ρ gA) z‖ ≤ C / ‖z - (chartAt ℂ y) a‖ := by
  classical
  set c := chartAt ℂ y with hc
  set p : ℂ := c a with hp
  -- the planar growth bound near the pole
  obtain ⟨C₁, hC₁pos, hC₁⟩ := Work.Drive.exists_norm_gradient_le_of_logExpansion
    (u := fun w : ℂ => gA (c.symm w)) (H := H) (p := p) (ρ := δ) hδ hH hueq
  -- the far region: compact, and the clamped pullback is `C¹` there
  set K : Set ℂ := Metric.closedBall (c y) σ ∩ {z : ℂ | δ / 2 ≤ ‖z - p‖} with hKdef
  have hKc : IsCompact K := (isCompact_closedBall (c y) σ).inter_right
    (isClosed_le continuous_const (continuous_norm.comp (continuous_id.sub continuous_const)))
  have hcont : ContinuousOn (fun z : ℂ => gradient (Work.Drive.clampedPullback y ρ gA) z) K := by
    intro z hz
    have hzball : z ∈ Metric.ball (c y) ρ := by
      rw [Metric.mem_ball]
      exact lt_of_le_of_lt (Metric.mem_closedBall.mp hz.1) hσρ
    have hzright : c (c.symm z) = z := c.right_inv (htgt hzball)
    have hzsrc : c.symm z ∈ c.source := c.map_target (htgt hzball)
    have hzΩ : c.symm z ∈ Ω := by
      refine hballΩ ⟨hzsrc, ?_⟩
      rw [Set.mem_preimage, hzright]; exact hzball
    have hzne : c.symm z ≠ a := by
      intro h
      have hpz : p = z := by rw [hp, ← h, hzright]
      have h0 : ‖z - p‖ = 0 := by rw [hpz]; simp
      have h2 : δ / 2 ≤ ‖z - p‖ := hz.2
      rw [h0] at h2
      linarith
    have hharm : Submission.HarmonicOnXAt gA (c.symm z) := hgA.2.1 _ ⟨hzΩ, hzne⟩
    have hH' : InnerProductSpace.HarmonicAt (fun w : ℂ => gA (c.symm w)) z := by
      have h := (Submission.HarmonicOnXAt_iff_chart (u := gA) (x := c.symm z) (y := y) hzsrc).mp
        hharm
      rwa [hzright] at h
    have h1 : ContinuousAt (fun w : ℂ => fderiv ℝ (fun u : ℂ => gA (c.symm u)) w) z :=
      hH'.1.continuousAt_fderiv (by norm_num)
    have h2 : ContinuousAt (fun w : ℂ => gradient (fun u : ℂ => gA (c.symm u)) w) z := by
      simpa only [gradient, Function.comp_def] using
        (InnerProductSpace.toDual ℝ ℂ).symm.continuous.continuousAt.comp h1
    exact (h2.congr_of_eventuallyEq (clamped_eq_unclamped_of_mem_ball (ρ := ρ) (g := gA) (y := y)
      hzball)).continuousWithinAt
  obtain ⟨M, hM⟩ := hKc.exists_bound_of_continuousOn hcont
  set M' : ℝ := max M 0 with hM'def
  have hM'nonneg : 0 ≤ M' := le_max_right _ _
  set R : ℝ := σ + ‖c y - p‖ with hRdef
  have hCpos : 0 < max C₁ (M' * R) + 1 := by
    have := le_max_left C₁ (M' * R); linarith [hC₁pos]
  refine ⟨max C₁ (M' * R) + 1, hCpos, fun z hz hzp => ?_⟩
  have hzR : ‖z - p‖ ≤ R := by
    have h1 : ‖z - c y‖ ≤ σ := by rw [← dist_eq_norm]; exact Metric.mem_closedBall.mp hz
    calc ‖z - p‖ = ‖(z - c y) + (c y - p)‖ := by ring_nf
      _ ≤ ‖z - c y‖ + ‖c y - p‖ := norm_add_le _ _
      _ ≤ R := by rw [hRdef]; linarith
  have hCge : C₁ ≤ max C₁ (M' * R) + 1 := by
    linarith [le_max_left C₁ (M' * R)]
  rcases lt_or_ge ‖z - p‖ (δ / 2) with hnear | hfar
  · have hzb : z ∈ Metric.ball p (δ / 2) := Metric.mem_ball.mpr (by rw [dist_eq_norm]; exact hnear)
    have hzball : z ∈ Metric.ball (c y) ρ := by
      rw [Metric.mem_ball]; exact lt_of_le_of_lt (Metric.mem_closedBall.mp hz) hσρ
    have hcl := clamped_eq_unclamped_of_mem_ball (ρ := ρ) (g := gA) (y := y) hzball
    have hgrad : gradient (Work.Drive.clampedPullback y ρ gA) z
        = gradient (fun u : ℂ => gA (c.symm u)) z := hcl.self_of_nhds
    rw [hgrad]
    refine le_trans (hC₁ z hzb hzp) ?_
    have hpos : 0 < ‖z - p‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hzp)
    apply div_le_div_of_nonneg_right ?_ (le_of_lt hpos)
    linarith [le_max_left C₁ (M' * R)]
  · have hzK : z ∈ K := ⟨hz, hfar⟩
    have hbound : ‖gradient (Work.Drive.clampedPullback y ρ gA) z‖ ≤ M' :=
      le_trans (hM z hzK) (le_max_left M 0)
    refine le_trans hbound ?_
    have hpos : 0 < ‖z - p‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hzp)
    rw [le_div_iff₀ hpos]
    calc M' * ‖z - p‖ ≤ M' * R := mul_le_mul_of_nonneg_left hzR hM'nonneg
      _ ≤ max C₁ (M' * R) + 1 := by linarith [le_max_right C₁ (M' * R)]

/-- **Boundedness of the clamped chart pullback of a Green function in a chart avoiding the pole.**

If the pole lies outside the closed chart disc of radius `σ < ρ`, then the gradient of the clamped
pullback is bounded on that closed disc. -/
theorem exists_bound_clampedPullback_le_of_notMem {Ω : Set X} {a : X} {gA : X → ℝ}
    {y : X} {ρ σ : ℝ}
    (hgA : Work.SimplyConnected.ABS.IsGreenOn Ω a gA)
    (hσρ : σ < ρ)
    (htgt : Metric.ball ((chartAt ℂ y) y) ρ ⊆ (chartAt ℂ y).target)
    (hballΩ : Submission.chartBall (chartAt ℂ y) ((chartAt ℂ y) y) ρ ⊆ Ω)
    (havoid : a ∉ Submission.chartClosedBall (chartAt ℂ y) ((chartAt ℂ y) y) σ) :
    ∃ C : ℝ, 0 < C ∧ ∀ z ∈ Metric.closedBall ((chartAt ℂ y) y) σ,
      ‖gradient (Work.Drive.clampedPullback y ρ gA) z‖ ≤ C := by
  classical
  have hcont : ContinuousOn (fun z : ℂ => gradient (Work.Drive.clampedPullback y ρ gA) z)
      (Metric.closedBall ((chartAt ℂ y) y) σ) := by
    intro z hz
    have hzball : z ∈ Metric.ball ((chartAt ℂ y) y) ρ := by
      rw [Metric.mem_ball]
      exact lt_of_le_of_lt (Metric.mem_closedBall.mp hz) hσρ
    have hzright : (chartAt ℂ y) ((chartAt ℂ y).symm z) = z := (chartAt ℂ y).right_inv (htgt hzball)
    have hzsrc : (chartAt ℂ y).symm z ∈ (chartAt ℂ y).source :=
      (chartAt ℂ y).map_target (htgt hzball)
    have hzΩ : (chartAt ℂ y).symm z ∈ Ω := by
      refine hballΩ ⟨hzsrc, ?_⟩
      rw [Set.mem_preimage, hzright]; exact hzball
    have hzne : (chartAt ℂ y).symm z ≠ a := by
      intro h
      refine havoid (Submission.mem_chartClosedBall.mpr ⟨?_, ?_⟩)
      · rw [← h]; exact hzsrc
      · rw [← h, hzright]; exact hz
    have hharm : Submission.HarmonicOnXAt gA ((chartAt ℂ y).symm z) := hgA.2.1 _ ⟨hzΩ, hzne⟩
    have hH' : InnerProductSpace.HarmonicAt
        (fun w : ℂ => gA ((chartAt ℂ y).symm w)) z := by
      have h := (Submission.HarmonicOnXAt_iff_chart (u := gA) (x := (chartAt ℂ y).symm z)
        (y := y) hzsrc).mp hharm
      rwa [hzright] at h
    have h1 : ContinuousAt
        (fun w : ℂ => fderiv ℝ (fun u : ℂ => gA ((chartAt ℂ y).symm u)) w) z :=
      hH'.1.continuousAt_fderiv (by norm_num)
    have h2 : ContinuousAt (fun w : ℂ => gradient (fun u : ℂ => gA ((chartAt ℂ y).symm u)) w) z := by
      simpa only [gradient, Function.comp_def] using
        (InnerProductSpace.toDual ℝ ℂ).symm.continuous.continuousAt.comp h1
    exact (h2.congr_of_eventuallyEq (clamped_eq_unclamped_of_mem_ball (ρ := ρ) (g := gA) (y := y)
      hzball)).continuousWithinAt
  obtain ⟨M, hM⟩ := (isCompact_closedBall ((chartAt ℂ y) y) σ).exists_bound_of_continuousOn hcont
  exact ⟨max M 0 + 1, by positivity, fun z hz =>
    le_trans (hM z hz) (by linarith [le_max_left M 0])⟩


/-! ## 5. `PairIntegrable` certificates from growth bounds on the support of the weight -/

/-- **`PairIntegrable` from growth bounds required only on the support of the weight.**  This is the
form in which the pole expansion of a Green function gives the integrability certificates: the
weight `W` (clamped at `σ`) is supported in a compact set on which the gradient of the clamped
`f` is bounded by `C/‖z-p‖` and the gradient of the clamped `χ` by `K`. -/
theorem pairIntegrable_of_support_growth' {x : X} {ρ σ : ℝ} {W f χ : X → ℝ} {p : ℂ} {C K : ℝ}
    (hC : 0 ≤ C) (hK : 0 ≤ K)
    (hWc : Continuous (Work.Drive.clampedPullback x σ W))
    (hWcs : HasCompactSupport (Work.Drive.clampedPullback x σ W))
    (hf : ∀ᵐ z ∂(volume : Measure ℂ), z ∈ tsupport (Work.Drive.clampedPullback x σ W) →
      ‖gradient (Work.Drive.clampedPullback x ρ f) z‖ ≤ C / ‖z - p‖)
    (hχbd : ∀ᵐ z ∂(volume : Measure ℂ), z ∈ tsupport (Work.Drive.clampedPullback x σ W) →
      ‖gradient (Work.Drive.clampedPullback x ρ χ) z‖ ≤ K)
    (hmeas : AEStronglyMeasurable (fun z : ℂ => inner (𝕜 := ℝ)
      (gradient (Work.Drive.clampedPullback x ρ f) z)
      (gradient (Work.Drive.clampedPullback x ρ χ) z)) volume) :
    Work.Drive.PairIntegrable x ρ σ W f χ := by
  rw [Work.Drive.PairIntegrable]
  have hmaj : Integrable (fun z : ℂ =>
      C * K * ((‖z - p‖)⁻¹ * ‖Work.Drive.clampedPullback x σ W z‖)) :=
    ((Work.Analysis.integrable_inv_norm_mul_of_hasCompactSupport p
      (fun z => ‖Work.Drive.clampedPullback x σ W z‖) hWc.norm hWcs.norm).const_mul (C * K))
  refine hmaj.mono' (hWc.aestronglyMeasurable.mul hmeas) ?_
  filter_upwards [hf, hχbd] with z hfz hχz
  rw [norm_mul, Real.norm_eq_abs]
  by_cases hW0 : Work.Drive.clampedPullback x σ W z = 0
  · have hz0 : |Work.Drive.clampedPullback x σ W z| = 0 := by rw [hW0]; simp
    rw [hz0, zero_mul]
    positivity
  · have hz : z ∈ tsupport (Work.Drive.clampedPullback x σ W) :=
      subset_tsupport _ (Function.mem_support.mpr hW0)
    have h1 := hfz hz
    have h2 := hχz hz
    have h3 : ‖inner (𝕜 := ℝ) (gradient (Work.Drive.clampedPullback x ρ f) z)
        (gradient (Work.Drive.clampedPullback x ρ χ) z)‖ ≤ (C / ‖z - p‖) * K :=
      (norm_inner_le_norm _ _).trans
        (mul_le_mul h1 h2 (norm_nonneg _) (div_nonneg hC (norm_nonneg _)))
    calc ‖Work.Drive.clampedPullback x σ W z‖
          * ‖inner (𝕜 := ℝ) (gradient (Work.Drive.clampedPullback x ρ f) z)
            (gradient (Work.Drive.clampedPullback x ρ χ) z)‖
        ≤ ‖Work.Drive.clampedPullback x σ W z‖ * ((C / ‖z - p‖) * K) :=
          mul_le_mul_of_nonneg_left h3 (abs_nonneg _)
      _ = C * K * ((‖z - p‖)⁻¹ * ‖Work.Drive.clampedPullback x σ W z‖) := by
          rw [div_eq_mul_inv]; ring

/-! ## 6. Planar integrability of `⟪∇f, ∇χ⟫` with a `1/‖z-p‖` growth bound -/

/-- **Integrability of `z ↦ ⟪∇f z, ∇χ z⟫`** when `χ` is `C¹` with compact support and `∇f` grows at
most like the inverse distance to `p` on the support of `χ`. -/
theorem integrable_inner_gradient_of_growth' {f χ : ℂ → ℝ} {p : ℂ} {C : ℝ} (hC : 0 ≤ C)
    (hfmeas : AEStronglyMeasurable (fun z : ℂ => gradient f z) volume)
    (hχc1 : ContDiff ℝ 1 χ) (hχcs : HasCompactSupport χ)
    (hbd : ∀ᵐ z ∂(volume : Measure ℂ), z ∈ tsupport χ → ‖gradient f z‖ ≤ C / ‖z - p‖) :
    Integrable (fun z : ℂ => inner (𝕜 := ℝ) (gradient f z) (gradient χ z)) := by
  have hgcont : Continuous (gradient χ) :=
    Work.Drive.GreenRung.continuous_gradient_of_contDiff_one hχc1
  have hgcs : HasCompactSupport (gradient χ) :=
    IsCompact.of_isClosed_subset hχcs (isClosed_tsupport _)
      (Work.Analysis.Harmonic.tsupport_gradient_subset χ)
  have hmaj : Integrable (fun z : ℂ => C * ((‖z - p‖)⁻¹ * ‖gradient χ z‖)) :=
    (Work.Analysis.integrable_inv_norm_mul_of_hasCompactSupport p (fun z => ‖gradient χ z‖)
      hgcont.norm hgcs.norm).const_mul C
  refine hmaj.mono' (hfmeas.inner hgcont.aestronglyMeasurable) ?_
  filter_upwards [hbd] with z hz
  by_cases h0 : gradient χ z = 0
  · rw [h0, inner_zero_right, norm_zero]
    exact mul_nonneg hC (mul_nonneg (inv_nonneg.mpr (norm_nonneg _)) (norm_nonneg _))
  · have hz' : z ∈ tsupport χ :=
      Work.Analysis.Harmonic.tsupport_gradient_subset χ
        (subset_tsupport _ (Function.mem_support.mpr h0))
    have h1 := hz hz'
    calc ‖inner (𝕜 := ℝ) (gradient f z) (gradient χ z)‖
        ≤ ‖gradient f z‖ * ‖gradient χ z‖ := norm_inner_le_norm _ _
      _ ≤ (C / ‖z - p‖) * ‖gradient χ z‖ := mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
      _ = C * ((‖z - p‖)⁻¹ * ‖gradient χ z‖) := by rw [div_eq_mul_inv]; ring

end GrowthBounds

/-! ## 7. Support bound for a clamped chart pullback -/

/-- If `w` is supported in the chart ball of radius `σ` around the base point, then the clamped
pullback of `w` at the (larger) radius `ρ` is supported in the closed ball of radius `σ`. -/
theorem tsupport_clampedPullback_subset_closedBall' {y : X} {ρ σ : ℝ} {w : X → ℝ}
    (htgt : Metric.ball ((chartAt ℂ y) y) ρ ⊆ (chartAt ℂ y).target)
    (hsupp : tsupport w ⊆
      Submission.chartBall (chartAt ℂ y) ((chartAt ℂ y) y) σ) :
    tsupport (Work.Drive.clampedPullback y ρ w) ⊆ Metric.closedBall ((chartAt ℂ y) y) σ := by
  refine closure_minimal (fun z hz => ?_) Metric.isClosed_closedBall
  rw [Function.mem_support] at hz
  have hzρ : z ∈ Metric.ball ((chartAt ℂ y) y) ρ := by
    by_contra h
    exact hz (Work.Drive.clampedPullback_apply_of_notMem h)
  have hwz : w ((chartAt ℂ y).symm z) ≠ 0 := by
    intro h0
    exact hz (by rw [Work.Drive.clampedPullback_apply_of_mem hzρ, h0])
  have hmem : (chartAt ℂ y).symm z ∈
      Submission.chartBall (chartAt ℂ y) ((chartAt ℂ y) y) σ :=
    hsupp (subset_tsupport w (Function.mem_support.mpr hwz))
  obtain ⟨-, hball⟩ := Submission.mem_chartBall.mp hmem
  rw [(chartAt ℂ y).right_inv (htgt hzρ)] at hball
  exact Metric.ball_subset_closedBall hball

end Work.Kernel.PS
