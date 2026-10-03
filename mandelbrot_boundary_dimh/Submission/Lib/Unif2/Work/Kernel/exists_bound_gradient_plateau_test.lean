import Mathlib
import Submission.Lib.Unif2.RiemannSurface
import Submission.Lib.Unif2.Work.SimplyConnected.ABS.Defs
import Submission.Lib.Unif2.Work.Drive.greenEnergyChart
import Submission.Lib.Unif2.Work.Analysis.gradient_comp_scalar
import Submission.Lib.Unif2.Work.Kernel.GreenCover

/-!
# A bound for the gradient of the plateau test function of the singular pole identity

Statement requested by the pole-identity route (`Work.Kernel.pairing_pole_singular`): for the test
function

  `Ψ n x = if x = a then Θ n (Mb + n) else χ x * Θ n (gA x)`

of the singular pole identity — a plateau profile `Θ n` applied to the Green function `gA` (which has
a logarithmic pole at `a`), damped by a weight `χ` which equals `1` near `a` — the gradient of its
clamped chart pullback is bounded **on the support of a weight of the cover** by
`K₁ + B * ‖gradient (clamped chart pullback of gA)‖`.

## The mathematics

On the support of the weight the clamped pullbacks are the honest chart expressions, so everything is
reduced to a chart-ball computation.  There, for `x = (chartAt ℂ y).symm z ≠ a`, the chain rule and
the Leibniz rule give

  `∇ (χ ∘ c⁻¹ · Θ ∘ gA ∘ c⁻¹) z = χ x • (deriv Θ (gA x) • ∇ (gA ∘ c⁻¹) z) + Θ (gA x) • ∇ (χ ∘ c⁻¹) z`,

and taking norms,

  `‖∇ (…)‖ ≤ |χ x| · |deriv Θ (gA x)| · ‖∇ (gA ∘ c⁻¹) z‖ + |Θ (gA x)| · ‖∇ (χ ∘ c⁻¹) z‖
            ≤ |χ x| · ‖∇ (clamped gA) z‖ + |gA x| · ‖∇ (χ ∘ c⁻¹) z‖`,

using `|deriv Θ| ≤ 1` and `|Θ w| ≤ |w|`.  The two remaining quantities are exactly the two outputs of
the boundedness lemma for the `χ`-terms below, which are bounded on the weight support.  The single
point `z = (chartAt ℂ y) a` (where the `if`, i.e. the value of `Ψ n` at the pole, may be out of step
with the smooth expression) is discarded: it is a null set, which is why the statement is an `∀ᵐ` one.

## Provenance of the local helpers

`Work.Kernel.exists_bound_chi_terms`, `…tsupport_clampedPullback_subset_closedBall_general` and
`…hasCompactSupport_clampedPullback` are proved below as *private* local copies written from scratch
for this file, so that this module depends only on the stable foundation
(`Submission.RiemannSurface`, `…ABS.Defs`, `…greenEnergyChart`, `…gradient_comp_scalar`,
`Work.Kernel.GreenCover`) and not on the volatile interface file that happened to contain them.
-/

open Set Metric Filter MeasureTheory
open scoped Manifold Topology Gradient ContDiff

set_option linter.unusedSectionVars false

noncomputable section

namespace Work.Kernel

/-! ## Local support lemmas for the clamped chart pullback -/

/-- **Support bound for a clamped chart pullback** — the clamping indicator alone forces the support
into the closed ball. -/
private theorem tsupport_clampedPullback_subset_closedBall_local {X : Type*} [TopologicalSpace X]
    [ChartedSpace ℂ X] {x : X} {ρ : ℝ} {f : X → ℝ} :
    tsupport (Work.Drive.clampedPullback x ρ f) ⊆ Metric.closedBall ((chartAt ℂ x) x) ρ := by
  refine closure_minimal (fun z hz => ?_) Metric.isClosed_closedBall
  rw [Function.mem_support] at hz
  refine Metric.ball_subset_closedBall ?_
  by_contra hzball
  exact hz (Work.Drive.clampedPullback_apply_of_notMem hzball)

/-- **Compact support of a clamped chart pullback** — the clamping makes it a subset of a closed
ball, hence compact, with no hypothesis at all on the function. -/
private theorem hasCompactSupport_clampedPullback_local {X : Type*} [TopologicalSpace X]
    [ChartedSpace ℂ X] {x : X} {σ : ℝ} {W : X → ℝ} :
    HasCompactSupport (Work.Drive.clampedPullback x σ W) := by
  rw [hasCompactSupport_def]
  refine IsCompact.of_isClosed_subset (isCompact_closedBall ((chartAt ℂ x) x) σ)
    isClosed_closure (closure_minimal (fun z hz => ?_) Metric.isClosed_closedBall)
  rw [Function.mem_support] at hz
  refine Metric.ball_subset_closedBall ?_
  by_contra hzball
  exact hz (Work.Drive.clampedPullback_apply_of_notMem hzball)

/-- **The `χ`-terms of the test-function gradient are bounded on the support of a weight.**  The
weight `χ` of the test function is `1` on a neighbourhood of the pole `a`, so the gradient of its
chart representative vanishes there; the only other term is `|gA|` times that gradient, which is
bounded on the compact support of the weight because `gA` is continuous off its pole and the support
does not meet the plateau neighbourhood of `a`. -/
private lemma exists_bound_chi_terms_local {X : Type*} [TopologicalSpace X] [T2Space X]
    [ChartedSpace ℂ X] [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]
    {Ω : Set X} {a y : X} {gA χ : X → ℝ} {ρ σ : ℝ} {W : X → ℝ}
    (hχc1 : ∀ x ∈ (chartAt ℂ y).source,
      ContDiffAt ℝ 1 (χ ∘ (chartAt ℂ y).symm) ((chartAt ℂ y) x))
    (hχ1 : χ =ᶠ[𝓝 a] 1)
    (hgA : Work.SimplyConnected.ABS.IsGreenOn Ω a gA)
    (htgt : Metric.ball ((chartAt ℂ y) y) ρ ⊆ (chartAt ℂ y).target)
    (hballΩ : Submission.chartBall (chartAt ℂ y) ((chartAt ℂ y) y) ρ ⊆ Ω)
    (hσρ : σ < ρ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z ∈ tsupport (Work.Drive.clampedPullback y σ W),
      |gA ((chartAt ℂ y).symm z)| *
        ‖gradient (fun w : ℂ => χ ((chartAt ℂ y).symm w)) z‖ ≤ C ∧
      |χ ((chartAt ℂ y).symm z)| ≤ C := by
  classical
  set c := chartAt ℂ y with hc
  obtain ⟨U, hU, hUχ⟩ := Filter.eventually_iff_exists_mem.mp hχ1
  obtain ⟨U₀, hU₀sub, hU₀open, haU₀⟩ := mem_nhds_iff.mp hU
  set O : Set ℂ := c '' (U₀ ∩ c.source) with hO
  have hOopen : IsOpen O :=
    c.isOpen_image_of_subset_source (hU₀open.inter c.open_source) inter_subset_right
  have hOeq : ∀ z ∈ O, χ (c.symm z) = 1 := by
    rintro z ⟨x, ⟨hxU, hxsrc⟩, rfl⟩
    rw [c.left_inv hxsrc]
    exact hUχ x (hU₀sub hxU)
  have hOgrad : ∀ z ∈ O, gradient (fun w : ℂ => χ (c.symm w)) z = 0 := by
    intro z hz
    have hev : (fun w : ℂ => χ (c.symm w)) =ᶠ[𝓝 z] (fun _ => (1 : ℝ)) := by
      filter_upwards [hOopen.mem_nhds hz] with w hw
      exact hOeq w hw
    rw [Filter.EventuallyEq.gradient_eq hev]
    simp [gradient]
  set F : ℂ → ℝ := fun z =>
    |gA (c.symm z)| * ‖gradient (fun w : ℂ => χ (c.symm w)) z‖ + |χ (c.symm z)| with hF
  have hScont : ContinuousOn F (tsupport (Work.Drive.clampedPullback y σ W)) := by
    intro z hzS
    have hzball : z ∈ Metric.ball (c y) ρ := by
      have h1 : z ∈ Metric.closedBall (c y) σ :=
        (tsupport_clampedPullback_subset_closedBall_local (x := y) (ρ := σ) (f := W)) hzS
      exact lt_of_le_of_lt (Metric.mem_closedBall.mp h1) hσρ
    have hztgt : z ∈ c.target := htgt hzball
    have hzsrc : c.symm z ∈ c.source := c.map_target hztgt
    have hzright : c (c.symm z) = z := c.right_inv hztgt
    have hχc1z : ContDiffAt ℝ 1 (fun w : ℂ => χ (c.symm w)) z := by
      have h := hχc1 (c.symm z) hzsrc
      rwa [hzright] at h
    by_cases hzO : z ∈ O
    · have hev : F =ᶠ[𝓝 z] (fun w => |χ (c.symm w)|) := by
        filter_upwards [hOopen.mem_nhds hzO] with w hw
        simp only [hF]
        rw [hOgrad w hw, norm_zero, mul_zero, zero_add]
      exact ((hχc1z.continuousAt.abs).congr_of_eventuallyEq hev).continuousWithinAt
    · have hxne : c.symm z ≠ a := by
        intro hcon
        refine hzO ⟨a, ⟨?_, ?_⟩, ?_⟩
        · exact haU₀
        · rw [← hcon]; exact hzsrc
        · rw [← hcon]; exact hzright
      have hxmem : c.symm z ∈ Submission.chartBall c (c y) ρ :=
        ⟨hzsrc, by rw [Set.mem_preimage, hzright]; exact hzball⟩
      have hxΩ : c.symm z ∈ Ω := hballΩ hxmem
      have hgAc : ContinuousAt (fun w : ℂ => gA (c.symm w)) z := by
        have hharm : Submission.HarmonicOnXAt gA (c.symm z) := hgA.2.1 _ ⟨hxΩ, hxne⟩
        have h2 := (Submission.HarmonicOnXAt_iff_chart (u := gA) (x := c.symm z) (y := y)
          hzsrc).mp hharm
        rw [hzright] at h2
        exact h2.1.continuousAt
      have hgc1 : ContinuousAt (fun w : ℂ => gradient (fun w : ℂ => χ (c.symm w)) w) z := by
        have h1 : ContinuousAt (fderiv ℝ (fun w : ℂ => χ (c.symm w))) z :=
          hχc1z.continuousAt_fderiv (by norm_num)
        simpa only [gradient, Function.comp_def] using
          (InnerProductSpace.toDual ℝ ℂ).symm.continuous.continuousAt.comp h1
      exact ((hgAc.abs.mul hgc1.norm).add hχc1z.continuousAt.abs).continuousWithinAt
  obtain ⟨C, hC⟩ := (hasCompactSupport_clampedPullback_local (x := y) (σ := σ) (W := W)).isCompact.exists_bound_of_continuousOn hScont
  refine ⟨max C 0, le_max_right _ _, fun z hz => ⟨?_, ?_⟩⟩
  · have h1 : F z ≤ C := le_trans (le_abs_self _) (hC z hz)
    have h2 : |gA (c.symm z)| * ‖gradient (fun w : ℂ => χ (c.symm w)) z‖ ≤ F z := by
      simp only [hF]
      exact le_add_of_nonneg_right (abs_nonneg _)
    exact le_trans h2 (le_trans h1 (le_max_left _ _))
  · have h1 : F z ≤ C := le_trans (le_abs_self _) (hC z hz)
    have h2 : |χ (c.symm z)| ≤ F z := by
      simp only [hF]
      exact le_add_of_nonneg_left (mul_nonneg (abs_nonneg _) (norm_nonneg _))
    exact le_trans h2 (le_trans h1 (le_max_left _ _))

/-! ## The gradient tools -/

/-- **The Leibniz rule for the gradient of a product of two real functions on `ℂ`.** -/
private lemma gradient_mul_real_local {f g : ℂ → ℝ} {z : ℂ}
    (hf : DifferentiableAt ℝ f z) (hg : DifferentiableAt ℝ g z) :
    gradient (fun w => f w * g w) z = f z • gradient g z + g z • gradient f z := by
  show (InnerProductSpace.toDual ℝ ℂ).symm (fderiv ℝ (f * g) z) = _
  rw [fderiv_mul hf hg, map_add, map_smul, map_smul]
  rfl

/-- **Pointwise bound for the gradient of the plateau test function.**  In a chart in which the chart
ball of radius `ρ` lies in the chart target and maps into `Ω`, at every point `z` of the open chart
ball whose preimage is not the pole `a`, the gradient of the clamped chart pullback of
`Ψ = if · = a then Θ t else χ · Θ (gA ·)` is bounded by `K₀ + K₀ ‖∇ (clamped gA)‖`, where `K₀`
dominates the two `χ`-terms `|gA| ‖∇χ‖` and `|χ|` of `exists_bound_chi_terms_local`. -/
lemma norm_gradient_plateau_clamped_le {X : Type*} [TopologicalSpace X] [T2Space X]
    [ChartedSpace ℂ X] [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X] [DecidableEq X]
    {Ω : Set X} {a y : X} {gA χ : X → ℝ} {Θ : ℝ → ℝ} {t ρ : ℝ}
    (hgA : Work.SimplyConnected.ABS.IsGreenOn Ω a gA)
    (hχc1 : ∀ x ∈ (chartAt ℂ y).source,
      ContDiffAt ℝ 1 (χ ∘ (chartAt ℂ y).symm) ((chartAt ℂ y) x))
    (hΘc1 : ContDiff ℝ 1 Θ)
    (hΘder : ∀ w : ℝ, 0 ≤ deriv Θ w ∧ deriv Θ w ≤ 1)
    (hΘabs : ∀ w : ℝ, |Θ w| ≤ |w|)
    (htgt : Metric.ball ((chartAt ℂ y) y) ρ ⊆ (chartAt ℂ y).target)
    (hballΩ : Submission.chartBall (chartAt ℂ y) ((chartAt ℂ y) y) ρ ⊆ Ω)
    {z : ℂ} (hz : z ∈ Metric.ball ((chartAt ℂ y) y) ρ)
    (hza : (chartAt ℂ y).symm z ≠ a) {K₀ : ℝ}
    (hKgm : |gA ((chartAt ℂ y).symm z)| *
        ‖gradient (fun w : ℂ => χ ((chartAt ℂ y).symm w)) z‖ ≤ K₀)
    (hKχ : |χ ((chartAt ℂ y).symm z)| ≤ K₀) :
    ‖gradient (Work.Drive.clampedPullback y ρ
        (fun x : X => if x = a then Θ t else χ x * Θ (gA x))) z‖
      ≤ K₀ + K₀ * ‖gradient (Work.Drive.clampedPullback y ρ gA) z‖ := by
  have hztgt : z ∈ (chartAt ℂ y).target := htgt hz
  have hzsrc : (chartAt ℂ y).symm z ∈ (chartAt ℂ y).source := (chartAt ℂ y).map_target hztgt
  have hzri : (chartAt ℂ y) ((chartAt ℂ y).symm z) = z := (chartAt ℂ y).right_inv hztgt
  have hxΩ : (chartAt ℂ y).symm z ∈ Ω :=
    hballΩ ⟨hzsrc, by rw [Set.mem_preimage, hzri]; exact hz⟩
  have hdiffχ : DifferentiableAt ℝ (fun w : ℂ => χ ((chartAt ℂ y).symm w)) z := by
    have h := hχc1 ((chartAt ℂ y).symm z) hzsrc
    rw [hzri] at h
    exact h.differentiableAt (by norm_num)
  have hdiffg : DifferentiableAt ℝ (fun w : ℂ => gA ((chartAt ℂ y).symm w)) z := by
    have hharm : Submission.HarmonicOnXAt gA ((chartAt ℂ y).symm z) := hgA.2.1 _ ⟨hxΩ, hza⟩
    have h := (Submission.HarmonicOnXAt_iff_chart (u := gA) (x := (chartAt ℂ y).symm z)
      (y := y) hzsrc).mp hharm
    rw [hzri] at h
    exact h.1.differentiableAt (by norm_num)
  have hdiffΘ : DifferentiableAt ℝ Θ (gA ((chartAt ℂ y).symm z)) :=
    hΘc1.differentiable (by norm_num) _
  have hgrad1 : gradient (Work.Drive.clampedPullback y ρ
        (fun x : X => if x = a then Θ t else χ x * Θ (gA x))) z
      = gradient (fun w : ℂ => if (chartAt ℂ y).symm w = a then Θ t
          else χ ((chartAt ℂ y).symm w) * Θ (gA ((chartAt ℂ y).symm w))) z := by
    apply Filter.EventuallyEq.gradient_eq
    filter_upwards [Metric.isOpen_ball.mem_nhds hz] with w hw
    rw [Work.Drive.clampedPullback_apply_of_mem hw]
  have hgrad2 : gradient (fun w : ℂ => if (chartAt ℂ y).symm w = a then Θ t
        else χ ((chartAt ℂ y).symm w) * Θ (gA ((chartAt ℂ y).symm w))) z
      = gradient (fun w : ℂ => χ ((chartAt ℂ y).symm w) * Θ (gA ((chartAt ℂ y).symm w))) z := by
    apply Filter.EventuallyEq.gradient_eq
    filter_upwards [((chartAt ℂ y).continuousAt_symm hztgt).eventually
      (isClosed_singleton.isOpen_compl.mem_nhds (by simpa using hza))] with w hw
    rw [if_neg (by simpa [Set.mem_compl_iff] using hw)]
  have hgrad4 : gradient (fun w : ℂ => gA ((chartAt ℂ y).symm w)) z
      = gradient (Work.Drive.clampedPullback y ρ gA) z := by
    apply Filter.EventuallyEq.gradient_eq
    filter_upwards [Metric.isOpen_ball.mem_nhds hz] with w hw
    rw [Work.Drive.clampedPullback_apply_of_mem hw]
  have hprod := gradient_mul_real_local hdiffχ (hdiffΘ.comp z hdiffg)
  simp only [Function.comp_def] at hprod
  have hchain := Work.Analysis.gradient_comp_scalar hdiffΘ hdiffg
  have hder : |deriv Θ (gA ((chartAt ℂ y).symm z))| ≤ 1 := by
    rw [abs_of_nonneg (hΘder _).1]; exact (hΘder _).2
  calc ‖gradient (Work.Drive.clampedPullback y ρ
        (fun x : X => if x = a then Θ t else χ x * Θ (gA x))) z‖
      = ‖gradient (fun w : ℂ => χ ((chartAt ℂ y).symm w) * Θ (gA ((chartAt ℂ y).symm w))) z‖ := by
        rw [hgrad1, hgrad2]
    _ = ‖χ ((chartAt ℂ y).symm z) • gradient (fun w : ℂ => Θ (gA ((chartAt ℂ y).symm w))) z
          + Θ (gA ((chartAt ℂ y).symm z)) • gradient (fun w : ℂ => χ ((chartAt ℂ y).symm w)) z‖ := by
        rw [hprod]
    _ ≤ ‖χ ((chartAt ℂ y).symm z) • gradient (fun w : ℂ => Θ (gA ((chartAt ℂ y).symm w))) z‖
          + ‖Θ (gA ((chartAt ℂ y).symm z)) • gradient (fun w : ℂ => χ ((chartAt ℂ y).symm w)) z‖ :=
        norm_add_le _ _
    _ = |χ ((chartAt ℂ y).symm z)| * ‖gradient (fun w : ℂ => Θ (gA ((chartAt ℂ y).symm w))) z‖
          + |Θ (gA ((chartAt ℂ y).symm z))|
            * ‖gradient (fun w : ℂ => χ ((chartAt ℂ y).symm w)) z‖ := by
        rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs]
    _ = |χ ((chartAt ℂ y).symm z)| * (|deriv Θ (gA ((chartAt ℂ y).symm z))| *
          ‖gradient (fun w : ℂ => gA ((chartAt ℂ y).symm w)) z‖)
          + |Θ (gA ((chartAt ℂ y).symm z))|
            * ‖gradient (fun w : ℂ => χ ((chartAt ℂ y).symm w)) z‖ := by
        rw [hchain, norm_smul, Real.norm_eq_abs]
    _ ≤ |χ ((chartAt ℂ y).symm z)| * ‖gradient (fun w : ℂ => gA ((chartAt ℂ y).symm w)) z‖
          + |gA ((chartAt ℂ y).symm z)|
            * ‖gradient (fun w : ℂ => χ ((chartAt ℂ y).symm w)) z‖ := by
        apply add_le_add
        · apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
          calc |deriv Θ (gA ((chartAt ℂ y).symm z))| *
                ‖gradient (fun w : ℂ => gA ((chartAt ℂ y).symm w)) z‖
              ≤ 1 * ‖gradient (fun w : ℂ => gA ((chartAt ℂ y).symm w)) z‖ :=
                mul_le_mul_of_nonneg_right hder (norm_nonneg _)
            _ = ‖gradient (fun w : ℂ => gA ((chartAt ℂ y).symm w)) z‖ := one_mul _
        · exact mul_le_mul_of_nonneg_right (hΘabs _) (norm_nonneg _)
    _ = |χ ((chartAt ℂ y).symm z)| * ‖gradient (Work.Drive.clampedPullback y ρ gA) z‖
          + |gA ((chartAt ℂ y).symm z)|
            * ‖gradient (fun w : ℂ => χ ((chartAt ℂ y).symm w)) z‖ := by
        rw [hgrad4]
    _ ≤ K₀ * ‖gradient (Work.Drive.clampedPullback y ρ gA) z‖ + K₀ := by
        apply add_le_add
        · exact mul_le_mul_of_nonneg_right hKχ (norm_nonneg _)
        · exact hKgm
    _ = K₀ + K₀ * ‖gradient (Work.Drive.clampedPullback y ρ gA) z‖ := by ring

/-! ## The requested statement -/

theorem exists_bound_gradient_plateau_test {X : Type*} [TopologicalSpace X] [T2Space X]
    [ChartedSpace ℂ X] [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X] [DecidableEq X]
    {ι : Type*} [Fintype ι] {Ω K : Set X} {a b : X} (E : Work.Kernel.GreenCover ι Ω K a b)
    {gA χ : X → ℝ} {Θ : ℕ → ℝ → ℝ} {Mb : ℝ}
    (hgA : Work.SimplyConnected.ABS.IsGreenOn Ω a gA)
    (hχc1 : ∀ k, ∀ x ∈ (chartAt ℂ (E.y k)).source,
      ContDiffAt ℝ 1 (χ ∘ (chartAt ℂ (E.y k)).symm) ((chartAt ℂ (E.y k)) x))
    (hχ1 : χ =ᶠ[nhds a] 1)
    (hΘc1 : ∀ n, ContDiff ℝ 1 (Θ n))
    (hΘder : ∀ (n : ℕ) (w : ℝ), 0 ≤ deriv (Θ n) w ∧ deriv (Θ n) w ≤ 1)
    (hΘabs : ∀ (n : ℕ) (w : ℝ), |Θ n w| ≤ |w|)
    (i : ι) :
    ∃ (K₁ B : ℝ), 0 ≤ K₁ ∧ 0 ≤ B ∧
      ∀ (n : ℕ), ∀ᵐ z ∂(MeasureTheory.volume : MeasureTheory.Measure ℂ),
        z ∈ tsupport (Work.Drive.clampedPullback (E.y i) (E.σ i) (E.ψ i)) →
          ‖gradient (Work.Drive.clampedPullback (E.y i) (E.ρ i)
              (fun x : X => if x = a then Θ n (Mb + n) else χ x * Θ n (gA x))) z‖
            ≤ K₁ + B * ‖gradient (Work.Drive.clampedPullback (E.y i) (E.ρ i) gA) z‖ := by
  classical
  -- The two `χ`-terms are bounded on the support of the weight `ψ i`.
  obtain ⟨C, hC0, hCbound⟩ := exists_bound_chi_terms_local
    (Ω := Ω) (a := a) (y := E.y i) (gA := gA) (χ := χ) (ρ := E.ρ i) (σ := E.σ i) (W := E.ψ i)
    (fun x hx => hχc1 i x hx) hχ1 hgA (E.htgt i) (E.hballΩ i) (E.hσρ i)
  refine ⟨C, C, hC0, hC0, fun n => ?_⟩
  -- Discard the single point `(chartAt ℂ (E.y i)) a`, where the `if` may disagree with `χ * Θ ∘ gA`.
  filter_upwards [MeasureTheory.compl_mem_ae_iff.mpr
    (MeasureTheory.measure_singleton ((chartAt ℂ (E.y i)) a))] with z hzca
  intro hzT
  -- The support of the weight of the cover lies in the open `ρ i`-ball of the chart.
  have hzball : z ∈ Metric.ball ((chartAt ℂ (E.y i)) (E.y i)) (E.ρ i) := by
    have h1 : z ∈ Metric.closedBall ((chartAt ℂ (E.y i)) (E.y i)) (E.σ i) :=
      tsupport_clampedPullback_subset_closedBall_local hzT
    exact lt_of_le_of_lt (Metric.mem_closedBall.mp h1) (E.hσρ i)
  -- ... and its preimage is not the pole, since `z ≠ (chartAt ℂ (E.y i)) a`.
  have hza : (chartAt ℂ (E.y i)).symm z ≠ a := by
    intro hcon
    refine hzca ?_
    have hztgt : z ∈ (chartAt ℂ (E.y i)).target := E.htgt i hzball
    have h2 : (chartAt ℂ (E.y i)) ((chartAt ℂ (E.y i)).symm z)
        = (chartAt ℂ (E.y i)) a := by rw [hcon]
    rw [(chartAt ℂ (E.y i)).right_inv hztgt] at h2
    exact Set.mem_singleton_iff.mpr h2
  have hb := hCbound z hzT
  exact norm_gradient_plateau_clamped_le (Ω := Ω) (a := a) (y := E.y i) (gA := gA) (χ := χ)
    (Θ := Θ n) (t := Mb + n) (ρ := E.ρ i) hgA (fun x hx => hχc1 i x hx) (hΘc1 n)
    (hΘder n) (hΘabs n) (E.htgt i) (E.hballΩ i) hzball hza hb.1 hb.2

end Work.Kernel
