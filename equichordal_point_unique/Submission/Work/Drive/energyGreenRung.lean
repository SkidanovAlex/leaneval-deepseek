import Mathlib
import Submission.Work.Drive.greenEnergyPairing
import Submission.Work.Drive.greenEnergyChart
import Submission.Work.Analysis.Harmonic.integral_inner_gradient_eq_zero

/-!
# The chart-local Green identity for the clamped Dirichlet pairing (`C¹` version)

This module supplies the `C¹` (rather than analytic) form of the clamped chart pullback and of the
chart-local Green identity, together with the elementary algebra of `Work.Drive.pairTerm` that the
energy route to the symmetry of the Green function needs:

* `Work.Drive.clampedPullback_mul`,
* `Work.Drive.gradient_mul_real` — the Leibniz rule for `gradient`,
* `Work.Drive.contDiff_clampedPullback_hasCompactSupport`,
* `Work.Drive.integral_inner_gradient_eq_zero_weight_one` — the chart-local Green identity in the
  form in which the energy route uses it: `pairTerm x ρ σ 1 h φ = 0`,
* `Work.Drive.pairTerm_symm` — symmetry of the pairing term in its two functions,
* `Work.Drive.pairTerm_ibp` — the integration-by-parts identity
  `pairTerm x ρ σ W f g = pairTerm x ρ σ 1 f (W * g) - pairTerm x ρ σ g f W`.
-/

open MeasureTheory Set Filter
open scoped Manifold Topology Gradient

noncomputable section

set_option linter.unusedVariables false

namespace Work.Drive

/- All declarations of this file live in their own namespace so that they cannot collide with the
simultaneously developed files of the fleet in `Work.Drive` (several of which prove the same
elementary facts). -/
namespace GreenRung

variable {X : Type*} [TopologicalSpace X] [T2Space X] [ChartedSpace ℂ X]

/-- The clamped pullback of a product is the product of the clamped pullbacks. -/
theorem clampedPullback_mul (x : X) (ρ : ℝ) (u v : X → ℝ) :
    clampedPullback x ρ (u * v) = clampedPullback x ρ u * clampedPullback x ρ v := by
  funext z
  by_cases hz : z ∈ Metric.ball ((chartAt ℂ x) x) ρ
  · simp only [Pi.mul_apply, clampedPullback, Set.indicator_of_mem hz]
  · simp only [Pi.mul_apply, clampedPullback, Set.indicator_of_notMem hz, zero_mul]

/-- The Leibniz rule for the gradient of a product of real-valued functions. -/
theorem gradient_mul_real {f g : ℂ → ℝ} {z : ℂ}
    (hf : DifferentiableAt ℝ f z) (hg : DifferentiableAt ℝ g z) :
    gradient (fun w => f w * g w) z = f z • gradient g z + g z • gradient f z := by
  show (InnerProductSpace.toDual ℝ ℂ).symm (fderiv ℝ (f * g) z) = _
  rw [fderiv_mul hf hg, map_add, map_smul, map_smul]
  rfl

/-- **Almost-everywhere differentiability of the clamped chart pullback** (from the `C¹` chart
pullback). -/
theorem contDiffAt_clampedPullback {x₀ : X} {u : X → ℝ} {ρ ρ₀ : ℝ}
    (hρ₀ρ : ρ₀ < ρ) (htgt : Metric.ball ((chartAt ℂ x₀) x₀) ρ ⊆ (chartAt ℂ x₀).target)
    (hu : ∀ x ∈ (chartAt ℂ x₀).source,
      ContDiffAt ℝ 1 (u ∘ (chartAt ℂ x₀).symm) ((chartAt ℂ x₀) x))
    (hsupp : tsupport u ⊆ (chartAt ℂ x₀) ⁻¹' (Metric.ball ((chartAt ℂ x₀) x₀) ρ₀)) :
    ∀ z : ℂ, ContDiffAt ℝ 1 (clampedPullback x₀ ρ u) z := by
  intro z
  by_cases hz : ρ₀ < dist z ((chartAt ℂ x₀) x₀)
  · have hopen : {w : ℂ | ρ₀ < dist w ((chartAt ℂ x₀) x₀)} ∈ 𝓝 z :=
      (isOpen_lt continuous_const (continuous_id.dist continuous_const)).mem_nhds hz
    have hev : clampedPullback x₀ ρ u =ᶠ[𝓝 z] 0 := by
      filter_upwards [hopen] with w hw
      by_cases hb : w ∈ Metric.ball ((chartAt ℂ x₀) x₀) ρ
      · rw [clampedPullback_apply_of_mem hb]
        by_contra hne
        have hmem : (chartAt ℂ x₀).symm w ∈ tsupport u :=
          subset_tsupport _ (Function.mem_support.mpr hne)
        have hthis := hsupp hmem
        rw [Set.mem_preimage, (chartAt ℂ x₀).right_inv (htgt hb)] at hthis
        exact absurd hthis (not_lt.mpr hw.le)
      · rw [clampedPullback_eq_zero_of_notMem_ball hb]
        simp
    exact ContDiffAt.congr_of_eventuallyEq contDiffAt_const hev
  · push_neg at hz
    have hmem : z ∈ Metric.ball ((chartAt ℂ x₀) x₀) ρ := by
      rw [Metric.mem_ball]; exact lt_of_le_of_lt hz hρ₀ρ
    have hsrc : (chartAt ℂ x₀).symm z ∈ (chartAt ℂ x₀).source :=
      (chartAt ℂ x₀).map_target (htgt hmem)
    have hright : (chartAt ℂ x₀) ((chartAt ℂ x₀).symm z) = z :=
      (chartAt ℂ x₀).right_inv (htgt hmem)
    have hG : ContDiffAt ℝ 1 (fun w : ℂ => u ((chartAt ℂ x₀).symm w)) z := by
      have := hu ((chartAt ℂ x₀).symm z) hsrc
      rwa [hright] at this
    refine hG.congr_of_eventuallyEq ?_
    filter_upwards [Metric.isOpen_ball.mem_nhds hmem] with w hw
    exact clampedPullback_apply_of_mem (x₀ := x₀) (ρ := ρ) (u := u) hw

/-- **Regularity of the clamped pullback (`C¹` version).** -/
theorem contDiff_clampedPullback_hasCompactSupport {x₀ : X} {u : X → ℝ} {ρ ρ₀ : ℝ}
    (hρ : 0 < ρ) (hρ₀ : 0 ≤ ρ₀) (hρ₀ρ : ρ₀ < ρ)
    (htgt : Metric.ball ((chartAt ℂ x₀) x₀) ρ ⊆ (chartAt ℂ x₀).target)
    (hu : ∀ x ∈ (chartAt ℂ x₀).source,
      ContDiffAt ℝ 1 (u ∘ (chartAt ℂ x₀).symm) ((chartAt ℂ x₀) x))
    (hsupp : tsupport u ⊆ (chartAt ℂ x₀) ⁻¹' (Metric.ball ((chartAt ℂ x₀) x₀) ρ₀)) :
    ContDiff ℝ 1 (clampedPullback x₀ ρ u) ∧ HasCompactSupport (clampedPullback x₀ ρ u) := by
  constructor
  · rw [contDiff_iff_contDiffAt]
    exact contDiffAt_clampedPullback hρ₀ρ htgt hu hsupp
  · rw [hasCompactSupport_def]
    refine IsCompact.of_isClosed_subset (isCompact_closedBall ((chartAt ℂ x₀) x₀) ρ)
      isClosed_closure (closure_minimal ?_ Metric.isClosed_closedBall)
    intro w hw
    by_contra hw'
    rw [Metric.mem_closedBall, not_le] at hw'
    exact hw (clampedPullback_eq_zero_of_lt_dist htgt hsupp (lt_trans hρ₀ρ hw'))

/-- If `u` vanishes near the point of the chart corresponding to `z`, then the clamped pullback of
`u` vanishes near `z`. -/
theorem notMem_tsupport_clampedPullback {x : X} {ρ : ℝ} {u : X → ℝ} {z : ℂ}
    (hz : z ∈ (chartAt ℂ x).target)
    (h : (chartAt ℂ x).symm z ∉ tsupport u) :
    z ∉ tsupport (clampedPullback x ρ u) := by
  have hy : (chartAt ℂ x).symm z ∈ (chartAt ℂ x).source := (chartAt ℂ x).map_target hz
  have hright : (chartAt ℂ x) ((chartAt ℂ x).symm z) = z := (chartAt ℂ x).right_inv hz
  -- `u` vanishes on a neighbourhood `V` of the point of the chart
  obtain ⟨V, hVmem, hVzero⟩ : ∃ V : Set X, V ∈ 𝓝 ((chartAt ℂ x).symm z) ∧ ∀ w ∈ V, u w = 0 :=
    ⟨(tsupport u)ᶜ, (isClosed_tsupport u).isOpen_compl.mem_nhds h,
      fun w hw => image_eq_zero_of_notMem_tsupport hw⟩
  have hVsrc : V ∩ (chartAt ℂ x).source ∈ 𝓝 ((chartAt ℂ x).symm z) :=
    Filter.inter_mem hVmem ((chartAt ℂ x).open_source.mem_nhds hy)
  have hWmem : (chartAt ℂ x) '' (V ∩ (chartAt ℂ x).source) ∈ 𝓝 z := by
    have := (chartAt ℂ x).image_mem_nhds hy hVsrc
    rwa [hright] at this
  have hWzero : ∀ w ∈ (chartAt ℂ x) '' (V ∩ (chartAt ℂ x).source),
      clampedPullback x ρ u w = 0 := by
    rintro w ⟨y', hy', rfl⟩
    by_cases hb : (chartAt ℂ x) y' ∈ Metric.ball ((chartAt ℂ x) x) ρ
    · rw [clampedPullback_apply_of_mem hb, (chartAt ℂ x).left_inv hy'.2]
      exact hVzero y' hy'.1
    · rw [clampedPullback_eq_zero_of_notMem_ball hb]
  have hdisj : Function.support (clampedPullback x ρ u)
      ∩ (chartAt ℂ x) '' (V ∩ (chartAt ℂ x).source) = ∅ := by
    rw [Set.eq_empty_iff_forall_notMem]
    rintro w ⟨hw1, hw2⟩
    rw [Function.mem_support] at hw1
    exact hw1 (hWzero w hw2)
  intro hcon
  obtain ⟨w, hw1, hw2⟩ := mem_closure_iff_nhds.mp hcon _ hWmem
  exact (Set.eq_empty_iff_forall_notMem.mp hdisj) w ⟨hw2, hw1⟩

/-- If `z` lies in the topological support of the clamped pullback of `u` (and strictly inside the
clamping ball), then the corresponding point of the chart lies in the topological support of `u`. -/
theorem symm_mem_tsupport_of_mem_tsupport_clampedPullback {x : X} {ρ : ℝ} {u : X → ℝ} {z : ℂ}
    (htgt : Metric.ball ((chartAt ℂ x) x) ρ ⊆ (chartAt ℂ x).target)
    (hzρ : dist z ((chartAt ℂ x) x) < ρ)
    (hz : z ∈ tsupport (clampedPullback x ρ u)) :
    (chartAt ℂ x).symm z ∈ tsupport u := by
  by_contra hcon
  exact notMem_tsupport_clampedPullback (htgt (Metric.mem_ball.mpr hzρ)) hcon hz

/-- The gradient of a `C¹` compactly supported function is continuous. -/
theorem continuous_gradient_of_contDiff_one {f : ℂ → ℝ} (hf : ContDiff ℝ 1 f) :
    Continuous (gradient f) := by
  have h1 : Continuous (fderiv ℝ f) := hf.continuous_fderiv (by norm_num)
  have h2 : Continuous fun z : ℂ => (InnerProductSpace.toDual ℝ ℂ).symm (fderiv ℝ f z) :=
    (InnerProductSpace.toDual ℝ ℂ).symm.continuous.comp h1
  have h3 : gradient f = fun z : ℂ => (InnerProductSpace.toDual ℝ ℂ).symm (fderiv ℝ f z) := by
    funext z
    rfl
  rw [h3]
  exact h2

/-- The gradient of a `C¹` compactly supported function is bounded. -/
theorem exists_norm_gradient_le_of_hasCompactSupport {f : ℂ → ℝ}
    (hf : ContDiff ℝ 1 f) (hfc : HasCompactSupport f) :
    ∃ C : ℝ, ∀ z : ℂ, ‖gradient f z‖ ≤ C :=
  Continuous.bounded_above_of_compact_support (continuous_gradient_of_contDiff_one hf)
    (IsCompact.of_isClosed_subset hfc (isClosed_tsupport _)
      (Work.Analysis.Harmonic.tsupport_gradient_subset f))

/-- **Integrability of the Dirichlet pairing integrand.**  A bounded function with compact support
times the inner product of the gradients of two `C¹` compactly supported functions is integrable. -/
theorem integrable_mul_inner_gradient_of_hasCompactSupport {A f g : ℂ → ℝ}
    (hA : Continuous A) (hAc : HasCompactSupport A)
    (hf : ContDiff ℝ 1 f) (hfc : HasCompactSupport f)
    (hg : ContDiff ℝ 1 g) (hgc : HasCompactSupport g) :
    Integrable (fun z : ℂ => A z * inner (𝕜 := ℝ) (gradient f z) (gradient g z)) := by
  obtain ⟨Cf, hCf⟩ := exists_norm_gradient_le_of_hasCompactSupport hf hfc
  obtain ⟨Cg, hCg⟩ := exists_norm_gradient_le_of_hasCompactSupport hg hgc
  obtain ⟨CA, hCA⟩ := Continuous.bounded_above_of_compact_support hA hAc
  have hsupp : Function.support (fun z : ℂ => A z * inner (𝕜 := ℝ) (gradient f z) (gradient g z))
      ⊆ tsupport A := by
    intro z hz
    by_contra hzA
    rw [Function.mem_support] at hz
    rw [image_eq_zero_of_notMem_tsupport hzA, zero_mul] at hz
    exact hz rfl
  rw [← integrableOn_iff_integrable_of_support_subset hsupp]
  have hmeas : AEStronglyMeasurable
      (fun z : ℂ => A z * inner (𝕜 := ℝ) (gradient f z) (gradient g z))
      (volume.restrict (tsupport A)) :=
    ((hA.mul (((continuous_gradient_of_contDiff_one hf).inner
      (continuous_gradient_of_contDiff_one hg)))).aestronglyMeasurable)
  refine IntegrableOn.of_bound hAc.isCompact.measure_lt_top hmeas (CA * (Cf * Cg)) ?_
  filter_upwards with z
  simp only [Real.norm_eq_abs, abs_mul]
  calc |A z| * |inner (𝕜 := ℝ) (gradient f z) (gradient g z)|
      ≤ CA * (Cf * Cg) := by
        refine mul_le_mul (hCA z) ?_ (abs_nonneg _) (le_trans (norm_nonneg _) (hCA z))
        exact (abs_real_inner_le_norm _ _).trans (mul_le_mul (hCf z) (hCg z)
          (norm_nonneg _) (le_trans (norm_nonneg _) (hCf z)))
    _ = CA * (Cf * Cg) := rfl

/-- Almost-everywhere differentiability of a clamped chart pullback whose chart expression is
differentiable on the whole clamping ball. -/
theorem clampedPullback_differentiableAt_ae_of_differentiableOn {x : X} {ρ : ℝ} {u : X → ℝ}
    (htgt : Metric.ball ((chartAt ℂ x) x) ρ ⊆ (chartAt ℂ x).target)
    (hu : ∀ y ∈ (chartAt ℂ x) ⁻¹' Metric.ball ((chartAt ℂ x) x) ρ,
      DifferentiableAt ℝ (u ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) y)) :
    ∀ᵐ z ∂(volume : Measure ℂ), DifferentiableAt ℝ (clampedPullback x ρ u) z := by
  rw [ae_iff]
  refine measure_mono_null (fun z hz => ?_) (MeasureTheory.Measure.addHaar_sphere volume
    ((chartAt ℂ x) x) ρ)
  by_cases hb : z ∈ Metric.ball ((chartAt ℂ x) x) ρ
  · have hev : (fun w : ℂ => u ((chartAt ℂ x).symm w)) =ᶠ[𝓝 z] clampedPullback x ρ u := by
      filter_upwards [Metric.isOpen_ball.mem_nhds hb] with w hw
      exact (clampedPullback_apply_of_mem (x₀ := x) (ρ := ρ) (u := u) hw).symm
    have hdiff : DifferentiableAt ℝ (fun w : ℂ => u ((chartAt ℂ x).symm w)) z := by
      have h := hu ((chartAt ℂ x).symm z)
        (by rw [Set.mem_preimage, (chartAt ℂ x).right_inv (htgt hb)]; exact hb)
      rwa [(chartAt ℂ x).right_inv (htgt hb)] at h
    exact absurd ((hev.differentiableAt_iff).mp hdiff) hz
  · by_cases hc : z ∈ Metric.closedBall ((chartAt ℂ x) x) ρ
    · rw [Metric.mem_sphere]
      rw [Metric.mem_closedBall] at hc
      exact le_antisymm hc (not_lt.mp hb)
    · have hev : clampedPullback x ρ u =ᶠ[𝓝 z] 0 := by
        filter_upwards [(Metric.isClosed_closedBall.isOpen_compl).mem_nhds hc] with w hw
        exact clampedPullback_eq_zero_of_notMem_ball (x := x) (ρ := ρ) (u := u)
          (fun hmem => hw (Metric.ball_subset_closedBall hmem))
      exact absurd ((hev.differentiableAt_iff).mpr (differentiableAt_const 0)) hz

/-- **The chart-local Green identity in the form used by the energy route.**

If `h` is harmonic on the topological support of the test function `φ` (which is `C¹` in the chart
with `tsupport φ` inside the ball of radius `σ < ρ`), then the pairing of the clamped pullbacks with
weight `1` vanishes. -/
theorem integral_inner_gradient_eq_zero_weight_one [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]
    {x₀ : X} {h φ : X → ℝ} {ρ σ : ℝ}
    (hσ : 0 ≤ σ) (hσρ : σ < ρ)
    (htgt : Metric.ball ((chartAt ℂ x₀) x₀) ρ ⊆ (chartAt ℂ x₀).target)
    (hφc1 : ∀ x ∈ (chartAt ℂ x₀).source,
      ContDiffAt ℝ 1 (φ ∘ (chartAt ℂ x₀).symm) ((chartAt ℂ x₀) x))
    (hφsupp : tsupport φ ⊆ (chartAt ℂ x₀) ⁻¹' (Metric.ball ((chartAt ℂ x₀) x₀) σ))
    (hhan : ∀ y ∈ tsupport φ, Submission.HarmonicOnXAt h y) :
    pairTerm x₀ ρ σ (fun _ : X => (1 : ℝ)) h φ = 0 := by
  have hρpos : 0 < ρ := lt_of_le_of_lt hσ hσρ
  obtain ⟨hφcd, hφcs⟩ :=
    contDiff_clampedPullback_hasCompactSupport (x₀ := x₀) (u := φ) (ρ := ρ) (ρ₀ := σ)
      hρpos hσ hσρ htgt hφc1 hφsupp
  have htsupp_sub : tsupport (clampedPullback x₀ ρ φ) ⊆
      Metric.closedBall ((chartAt ℂ x₀) x₀) σ := by
    rw [tsupport]
    refine closure_minimal ?_ Metric.isClosed_closedBall
    intro z hz
    rw [Function.mem_support] at hz
    rw [Metric.mem_closedBall]
    by_cases hb : z ∈ Metric.ball ((chartAt ℂ x₀) x₀) ρ
    · rw [clampedPullback_apply_of_mem hb] at hz
      have hmem : (chartAt ℂ x₀).symm z ∈ tsupport φ :=
        subset_tsupport _ (Function.mem_support.mpr hz)
      have hthis := hφsupp hmem
      rw [Set.mem_preimage, (chartAt ℂ x₀).right_inv (htgt hb)] at hthis
      exact le_of_lt hthis
    · rw [clampedPullback_eq_zero_of_notMem_ball hb] at hz
      exact absurd rfl hz
  have hae : (fun z : ℂ => clampedPullback x₀ σ (fun _ : X => (1 : ℝ)) z *
        inner (𝕜 := ℝ) (gradient (clampedPullback x₀ ρ h) z)
          (gradient (clampedPullback x₀ ρ φ) z))
      =ᵐ[volume] fun z : ℂ => inner (𝕜 := ℝ) (gradient (clampedPullback x₀ ρ h) z)
          (gradient (clampedPullback x₀ ρ φ) z) := by
    filter_upwards [compl_mem_ae_iff.mpr (MeasureTheory.Measure.addHaar_sphere volume
      ((chartAt ℂ x₀) x₀) σ)] with z hz
    have hne : dist z ((chartAt ℂ x₀) x₀) ≠ σ := fun hcon =>
      hz (by rw [Metric.mem_sphere]; exact hcon)
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have hmem : z ∈ Metric.ball ((chartAt ℂ x₀) x₀) σ := Metric.mem_ball.mpr hlt
      have h1 : clampedPullback x₀ σ (fun _ : X => (1 : ℝ)) z = 1 := by
        rw [clampedPullback_apply_of_mem hmem]
      rw [h1, one_mul]
    · have hnot : z ∉ tsupport (clampedPullback x₀ ρ φ) := fun hcon =>
        absurd (htsupp_sub hcon) (not_le.mpr hgt)
      have h2 : clampedPullback x₀ σ (fun _ : X => (1 : ℝ)) z = 0 := by
        rw [clampedPullback_eq_zero_of_notMem_ball (x := x₀) (ρ := σ)
          (u := fun _ => (1 : ℝ)) (z := z)
          (fun hmem => absurd (Metric.mem_ball.mp hmem) (not_lt.mpr (le_of_lt hgt)))]
      rw [Work.Analysis.Harmonic.gradient_eq_zero_of_notMem_tsupport hnot, h2]
      simp
  rw [pairTerm, integral_congr_ae hae]
  refine Work.Analysis.Harmonic.integral_inner_gradient_eq_zero ?_ hφcd hφcs
  intro z hz
  have hzball : z ∈ Metric.ball ((chartAt ℂ x₀) x₀) ρ :=
    Metric.closedBall_subset_ball hσρ (htsupp_sub hz)
  have hharm : Submission.HarmonicOnXAt h ((chartAt ℂ x₀).symm z) :=
    hhan _ (symm_mem_tsupport_of_mem_tsupport_clampedPullback htgt (Metric.mem_ball.mp hzball) hz)
  have hsrc : (chartAt ℂ x₀).symm z ∈ (chartAt ℂ x₀).source :=
    (chartAt ℂ x₀).map_target (htgt hzball)
  have hright : (chartAt ℂ x₀) ((chartAt ℂ x₀).symm z) = z :=
    (chartAt ℂ x₀).right_inv (htgt hzball)
  have hchart := (Submission.HarmonicOnXAt_iff_chart (X := X) (u := h)
    (x := (chartAt ℂ x₀).symm z) (y := x₀) hsrc).mp hharm
  rw [hright] at hchart
  have hev : (fun w : ℂ => h ((chartAt ℂ x₀).symm w)) =ᶠ[𝓝 z] clampedPullback x₀ ρ h := by
    filter_upwards [Metric.isOpen_ball.mem_nhds hzball] with w hw
    exact (clampedPullback_apply_of_mem (x₀ := x₀) (ρ := ρ) (u := h) hw).symm
  exact (InnerProductSpace.harmonicAt_congr_nhds hev).mp hchart

/-- Symmetry of the pairing term in its two functions. -/
theorem pairTerm_symm (x : X) (ρ σ : ℝ) (W f g : X → ℝ) :
    pairTerm x ρ σ W f g = pairTerm x ρ σ W g f := by
  rw [pairTerm, pairTerm]
  refine integral_congr_ae ?_
  filter_upwards with z
  rw [real_inner_comm]

/-- **The Leibniz rule for the Dirichlet pairing integrand.**  Away from the sphere of radius `σ`,
the integrand of `pairTerm x ρ σ W f g` is the difference of the integrands of
`pairTerm x ρ σ 1 f (W * g)` and of `pairTerm x ρ σ g f W`. -/
theorem pairTerm_ibp_integrand {x : X} {ρ σ : ℝ} {W f g : X → ℝ} {z : ℂ}
    (hσρ : σ < ρ)
    (hz : z ∉ Metric.sphere ((chartAt ℂ x) x) σ)
    (hWσ : DifferentiableAt ℝ (clampedPullback x σ W) z)
    (hf : DifferentiableAt ℝ (clampedPullback x ρ f) z)
    (hg : DifferentiableAt ℝ (clampedPullback x ρ g) z)
    (hWg : DifferentiableAt ℝ (clampedPullback x ρ (W * g)) z) :
    clampedPullback x σ W z *
        inner (𝕜 := ℝ) (gradient (clampedPullback x ρ f) z) (gradient (clampedPullback x ρ g) z)
      = clampedPullback x σ (fun _ : X => (1 : ℝ)) z *
          inner (𝕜 := ℝ) (gradient (clampedPullback x ρ f) z)
            (gradient (clampedPullback x ρ (W * g)) z)
        - clampedPullback x σ g z *
          inner (𝕜 := ℝ) (gradient (clampedPullback x ρ f) z) (gradient (clampedPullback x ρ W) z) := by
  have hne : dist z ((chartAt ℂ x) x) ≠ σ := fun hcon =>
    hz (by rw [Metric.mem_sphere]; exact hcon)
  rcases lt_or_gt_of_ne hne with hin | hout
  · have hmem : z ∈ Metric.ball ((chartAt ℂ x) x) σ := Metric.mem_ball.mpr hin
    have hmemρ : z ∈ Metric.ball ((chartAt ℂ x) x) ρ := Metric.mem_ball.mpr (lt_trans hin hσρ)
    have h1 : clampedPullback x σ (fun _ : X => (1 : ℝ)) z = 1 := by
      rw [clampedPullback_apply_of_mem hmem]
    have eW : clampedPullback x σ W =ᶠ[𝓝 z] clampedPullback x ρ W := by
      filter_upwards [Metric.isOpen_ball.mem_nhds hmem] with w hw
      rw [clampedPullback_eq_of_mem_ball (le_rfl) hw,
        clampedPullback_eq_of_mem_ball (le_of_lt hσρ) hw]
    have eg : clampedPullback x σ g =ᶠ[𝓝 z] clampedPullback x ρ g := by
      filter_upwards [Metric.isOpen_ball.mem_nhds hmem] with w hw
      rw [clampedPullback_eq_of_mem_ball (le_rfl) hw,
        clampedPullback_eq_of_mem_ball (le_of_lt hσρ) hw]
    have emul : clampedPullback x ρ (W * g)
        =ᶠ[𝓝 z] clampedPullback x σ W * clampedPullback x ρ g := by
      filter_upwards [Metric.isOpen_ball.mem_nhds hmem] with w hw
      simp only [Pi.mul_apply, clampedPullback_mul]
      rw [clampedPullback_eq_of_mem_ball (le_of_lt hσρ) hw,
        clampedPullback_eq_of_mem_ball (le_rfl) hw]
    have hgrad : gradient (clampedPullback x ρ (W * g)) z
        = clampedPullback x σ W z • gradient (clampedPullback x ρ g) z
          + clampedPullback x ρ g z • gradient (clampedPullback x σ W) z := by
      rw [Filter.EventuallyEq.gradient_eq emul]
      exact gradient_mul_real hWσ hg
    have egz : clampedPullback x σ g z = clampedPullback x ρ g z := eg.eq_of_nhds
    have hgW : gradient (clampedPullback x σ W) z = gradient (clampedPullback x ρ W) z :=
      Filter.EventuallyEq.gradient_eq eW
    rw [h1, hgrad, inner_add_right, inner_smul_right, inner_smul_right, egz, hgW]
    ring
  · have hnot : z ∉ Metric.ball ((chartAt ℂ x) x) σ := by
      rw [Metric.mem_ball]; exact not_lt.mpr (le_of_lt hout)
    have h1 : clampedPullback x σ (fun _ : X => (1 : ℝ)) z = 0 := by
      rw [clampedPullback_eq_zero_of_notMem_ball hnot]
    have h2 : clampedPullback x σ W z = 0 := clampedPullback_eq_zero_of_notMem_ball (u := W) hnot
    have h3 : clampedPullback x σ g z = 0 := clampedPullback_eq_zero_of_notMem_ball (u := g) hnot
    rw [h1, h2, h3]
    simp

/-- **Locality of the pairing term in the weight.**  If two weights agree on the topological support
of the second function, then the corresponding pairing terms agree: away from that support the
gradient of the (clamped) second function vanishes, and outside the clamping ball the weight is
irrelevant. -/
theorem pairTerm_congr_weight {x : X} {ρ σ : ℝ} {W W' f g : X → ℝ}
    (htgt : Metric.ball ((chartAt ℂ x) x) ρ ⊆ (chartAt ℂ x).target)
    (hσρ : σ < ρ)
    (h : ∀ y ∈ tsupport g, W y = W' y) :
    pairTerm x ρ σ W f g = pairTerm x ρ σ W' f g := by
  rw [pairTerm, pairTerm]
  refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
  dsimp only
  by_cases hb : z ∈ Metric.ball ((chartAt ℂ x) x) σ
  · by_cases hz : z ∈ tsupport (clampedPullback x ρ g)
    · have hzρ : z ∈ Metric.ball ((chartAt ℂ x) x) ρ :=
        Metric.ball_subset_ball (le_of_lt hσρ) hb
      have hy : (chartAt ℂ x).symm z ∈ tsupport g :=
        symm_mem_tsupport_of_mem_tsupport_clampedPullback htgt (Metric.mem_ball.mp hzρ) hz
      rw [clampedPullback_apply_of_mem hb, clampedPullback_apply_of_mem hb, h _ hy]
    · rw [Work.Analysis.Harmonic.gradient_eq_zero_of_notMem_tsupport hz, inner_zero_right,
        mul_zero, mul_zero]
  · simp only [clampedPullback_eq_zero_of_notMem_ball hb, zero_mul]

/-- **Integration by parts for the pairing term.** -/
theorem pairTerm_ibp {x : X} {ρ σ : ℝ} {W f g : X → ℝ} (hσρ : σ < ρ)
    (hWσ : ∀ᵐ z ∂(volume : Measure ℂ), DifferentiableAt ℝ (clampedPullback x σ W) z)
    (hf : ∀ᵐ z ∂(volume : Measure ℂ), DifferentiableAt ℝ (clampedPullback x ρ f) z)
    (hg : ∀ᵐ z ∂(volume : Measure ℂ), DifferentiableAt ℝ (clampedPullback x ρ g) z)
    (hWg : ∀ᵐ z ∂(volume : Measure ℂ), DifferentiableAt ℝ (clampedPullback x ρ (W * g)) z)
    (hi1 : PairIntegrable x ρ σ (fun _ : X => (1 : ℝ)) f (W * g))
    (hi2 : PairIntegrable x ρ σ g f W) :
    pairTerm x ρ σ W f g = pairTerm x ρ σ (fun _ : X => (1 : ℝ)) f (W * g)
      - pairTerm x ρ σ g f W := by
  rw [pairTerm, pairTerm, pairTerm, ← integral_sub hi1 hi2]
  refine integral_congr_ae ?_
  filter_upwards [hWσ, hf, hg, hWg, compl_mem_ae_iff.mpr
    (MeasureTheory.Measure.addHaar_sphere volume ((chartAt ℂ x) x) σ)] with z h1 h3 h4 h5 h6
  exact pairTerm_ibp_integrand (x := x) (ρ := ρ) (σ := σ) (W := W) (f := f) (g := g)
    hσρ h6 h1 h3 h4 h5

end GreenRung

end Work.Drive

end
