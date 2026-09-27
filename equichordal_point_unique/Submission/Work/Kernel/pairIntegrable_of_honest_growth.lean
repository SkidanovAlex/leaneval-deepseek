import Mathlib
import Submission.Work.Drive.greenEnergyPairing

/-!
# Integrability of a chart-local Dirichlet pairing term from honest growth bounds

`Work.Drive.PairIntegrable x ρ σ W f g` asks that the *clamped* pairing integrand
`clampedPullback x σ W · ⟨∇(clampedPullback x ρ f), ∇(clampedPullback x ρ g)⟩` be Lebesgue
integrable on the chart `ℂ`.

In practice the data available in a chart is never about the clamped objects but about the *honest*
chart pullbacks `W ∘ (chartAt ℂ x).symm`, `f ∘ (chartAt ℂ x).symm`, `g ∘ (chartAt ℂ x).symm`:

* the weight is continuous and bounded on the *open* ball of radius `σ` — in particular it need
  **not** vanish on the sphere, so the clamped weight is not continuous;
* the pairing `⟨∇(f ∘ symm), ∇(g ∘ symm)⟩` is continuous off a single point `p` and grows at most
  like `C₂ / ‖z - p‖` towards it.

This file shows that these honest hypotheses already force integrability:

* on the open ball of radius `ρ` the clamped pullback of a function agrees with the honest pullback
  on a neighbourhood of every point, hence the two gradients agree there *everywhere* (even at
  points where the function is not differentiable, `fderiv` of eventually equal functions is
  equal);
* the integrand is therefore the indicator of the small ball `σ` times the honest pairing, which is
  continuous on the open set `ball σ \ {p}` and has the single exception `p` (a null set);
* a continuous bump function `φ` with `φ = 1` on the closed `σ`-ball and compact support dominates
  the indicator, and `Work.Analysis.integrable_inv_norm_mul_of_hasCompactSupport` says
  `z ↦ ‖z - p‖⁻¹ * φ z` is integrable.

The measurability input is `measurable_indicator_of_isOpen_of_continuousOn` below, a small
Borel-measurability fact that Mathlib does not seem to record in this form.
-/

open MeasureTheory Set Metric Filter
open scoped Gradient Topology

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Work.Kernel

/-- **The indicator of an open set times a function continuous on it is Borel measurable.**
(Continuity at the boundary of `s` is neither needed nor available: off `s` the value is `0`.) -/
theorem measurable_indicator_of_isOpen_of_continuousOn {f : ℂ → ℝ} {s : Set ℂ}
    (hs : IsOpen s) (hf : ContinuousOn f s) : Measurable (s.indicator f) := by
  classical
  apply measurable_of_isOpen
  intro t ht
  obtain ⟨u, u_open, hu⟩ : ∃ u : Set ℂ, IsOpen u ∧ f ⁻¹' t ∩ s = u ∩ s :=
    continuousOn_iff'.1 hf t ht
  have hpre : (s.indicator f) ⁻¹' t
      = (f ⁻¹' t ∩ s) ∪ (if (0 : ℝ) ∈ t then sᶜ else ∅) := by
    ext z
    by_cases h0 : (0 : ℝ) ∈ t
    · rw [if_pos h0]
      by_cases hz : z ∈ s
      · rw [Set.mem_preimage, Set.indicator_of_mem hz]
        simp [hz]
      · rw [Set.mem_preimage, Set.indicator_of_notMem hz]
        simp [hz, h0]
    · rw [if_neg h0]
      by_cases hz : z ∈ s
      · rw [Set.mem_preimage, Set.indicator_of_mem hz]
        simp [hz]
      · rw [Set.mem_preimage, Set.indicator_of_notMem hz]
        simp [hz, h0]
  rw [hpre, hu]
  by_cases h0 : (0 : ℝ) ∈ t
  · rw [if_pos h0]
    exact (u_open.measurableSet.inter hs.measurableSet).union hs.isClosed_compl.measurableSet
  · simpa [if_neg h0] using u_open.measurableSet.inter hs.measurableSet

variable {X : Type*} [TopologicalSpace X] [T2Space X] [ChartedSpace ℂ X]

/-- **Gradients of the clamped and of the honest chart pullback agree on the ball of the clamp.**
The clamping only changes the function off the ball of radius `ρ`; inside it the two functions agree
on a neighbourhood of every point, so their Fréchet derivatives — and hence their gradients — are
equal, whether or not the function is differentiable there. -/
theorem gradient_clampedPullback_eq_of_mem_ball {x : X} {ρ : ℝ} {u : X → ℝ} {z : ℂ}
    (hz : z ∈ Metric.ball ((chartAt ℂ x) x) ρ) :
    gradient (Work.Drive.clampedPullback x ρ u) z
      = gradient (fun w : ℂ => u ((chartAt ℂ x).symm w)) z := by
  have hev : Work.Drive.clampedPullback x ρ u
      =ᶠ[𝓝 z] (fun w : ℂ => u ((chartAt ℂ x).symm w)) := by
    filter_upwards [Metric.isOpen_ball.mem_nhds hz] with w hw
    exact Work.Drive.clampedPullback_apply_of_mem hw
  exact hev.gradient_eq

/-- **Integrability of a chart-local Dirichlet pairing term, given a growth bound.**

The weight `W` is continuous and bounded by `C₁` on the open ball of radius `σ`; the honest pairing
of the chart pullbacks of `f` and `g` is continuous off `p` and bounded by `C₂ / ‖z - p‖` on the
ball of radius `σ`.  Then the clamped pairing integrand is integrable. -/
theorem pairIntegrable_of_honest_growth {X : Type*} [TopologicalSpace X] [T2Space X]
    [ChartedSpace ℂ X] {x : X} {ρ σ : ℝ} {W f g : X → ℝ} {p : ℂ} {C₁ C₂ : ℝ}
    (hσ : 0 ≤ σ) (hσρ : σ < ρ)
    (htgt : Metric.ball ((chartAt ℂ x) x) ρ ⊆ (chartAt ℂ x).target)
    (hWcont : ContinuousOn (fun z : ℂ => W ((chartAt ℂ x).symm z))
      (Metric.ball ((chartAt ℂ x) x) σ))
    (hWbd : ∀ z ∈ Metric.ball ((chartAt ℂ x) x) σ,
      ‖W ((chartAt ℂ x).symm z)‖ ≤ C₁)
    (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂)
    (hcont : ContinuousOn (fun z : ℂ => inner (𝕜 := ℝ)
        (gradient (fun w : ℂ => f ((chartAt ℂ x).symm w)) z)
        (gradient (fun w : ℂ => g ((chartAt ℂ x).symm w)) z))
      (Metric.ball ((chartAt ℂ x) x) σ \ {p}))
    (hgrad : ∀ z ∈ Metric.ball ((chartAt ℂ x) x) σ, z ≠ p →
      ‖inner (𝕜 := ℝ) (gradient (fun w : ℂ => f ((chartAt ℂ x).symm w)) z)
        (gradient (fun w : ℂ => g ((chartAt ℂ x).symm w)) z)‖ ≤ C₂ / ‖z - p‖) :
    Work.Drive.PairIntegrable x ρ σ W f g := by
  classical
  -- radii of the dominating bump: `σ < rIn < rOut < ρ`
  let rIn : ℝ := σ + (ρ - σ) / 3
  let rOut : ℝ := σ + 2 * (ρ - σ) / 3
  have hrIn_pos : 0 < rIn := by
    show 0 < σ + (ρ - σ) / 3
    linarith
  have hrIn_lt_rOut : rIn < rOut := by
    show σ + (ρ - σ) / 3 < σ + 2 * (ρ - σ) / 3
    linarith
  let φ : ContDiffBump ((chartAt ℂ x) x) := ⟨rIn, rOut, hrIn_pos, hrIn_lt_rOut⟩
  have hσ_le_rIn : σ ≤ rIn := by
    show σ ≤ σ + (ρ - σ) / 3
    linarith
  -- the honest pairing, and the integrand seen as `indicator (ball σ) J`
  let J : ℂ → ℝ := fun z => W ((chartAt ℂ x).symm z) *
      inner (𝕜 := ℝ) (gradient (fun w : ℂ => f ((chartAt ℂ x).symm w)) z)
        (gradient (fun w : ℂ => g ((chartAt ℂ x).symm w)) z)
  have hfun : (fun z : ℂ => Work.Drive.clampedPullback x σ W z *
        inner (𝕜 := ℝ) (gradient (Work.Drive.clampedPullback x ρ f) z)
          (gradient (Work.Drive.clampedPullback x ρ g) z))
      = Set.indicator (Metric.ball ((chartAt ℂ x) x) σ) J := by
    funext z
    by_cases hz : z ∈ Metric.ball ((chartAt ℂ x) x) σ
    · have hzρ : z ∈ Metric.ball ((chartAt ℂ x) x) ρ :=
        Metric.ball_subset_ball (le_of_lt hσρ) hz
      rw [Work.Drive.clampedPullback_apply_of_mem hz,
        gradient_clampedPullback_eq_of_mem_ball (x := x) (ρ := ρ) hzρ,
        gradient_clampedPullback_eq_of_mem_ball (x := x) (ρ := ρ) hzρ,
        Set.indicator_of_mem hz]
    · rw [Work.Drive.clampedPullback_apply_of_notMem hz, Set.indicator_of_notMem hz, zero_mul]
  -- measurability of the integrand
  have hJcont : ContinuousOn J (Metric.ball ((chartAt ℂ x) x) σ \ {p}) :=
    (hWcont.mono Set.sdiff_subset).mul hcont
  have hopen : IsOpen (Metric.ball ((chartAt ℂ x) x) σ \ {p}) := by
    rw [Set.sdiff_eq]
    exact Metric.isOpen_ball.inter isOpen_compl_singleton
  have hJmeas : Measurable (Set.indicator (Metric.ball ((chartAt ℂ x) x) σ) J) := by
    have hmeas₁ : Measurable (Set.indicator (Metric.ball ((chartAt ℂ x) x) σ \ {p}) J) :=
      measurable_indicator_of_isOpen_of_continuousOn hopen hJcont
    have hmeas₂ : Measurable
        (Set.indicator (Metric.ball ((chartAt ℂ x) x) σ ∩ {p}) J) := by
      have hset : MeasurableSet (Metric.ball ((chartAt ℂ x) x) σ ∩ {p}) :=
        Metric.isOpen_ball.measurableSet.inter (measurableSet_singleton p)
      have heq : Set.indicator (Metric.ball ((chartAt ℂ x) x) σ ∩ {p}) J
          = Set.indicator (Metric.ball ((chartAt ℂ x) x) σ ∩ {p}) (fun _ : ℂ => J p) := by
        funext z
        by_cases hz : z ∈ Metric.ball ((chartAt ℂ x) x) σ ∩ {p}
        · rw [Set.indicator_of_mem hz, Set.indicator_of_mem hz,
            Set.mem_singleton_iff.mp hz.2]
        · rw [Set.indicator_of_notMem hz, Set.indicator_of_notMem hz]
      rw [heq]
      exact Measurable.indicator measurable_const hset
    have hdec : Set.indicator (Metric.ball ((chartAt ℂ x) x) σ) J
        = Set.indicator (Metric.ball ((chartAt ℂ x) x) σ \ {p}) J
          + Set.indicator (Metric.ball ((chartAt ℂ x) x) σ ∩ {p}) J := by
      funext z
      by_cases hzs : z ∈ Metric.ball ((chartAt ℂ x) x) σ
      · by_cases hzp : z = p
        · have h1 : z ∉ Metric.ball ((chartAt ℂ x) x) σ \ {p} := by
            rw [Set.mem_sdiff]
            exact fun h => h.2 (Set.mem_singleton_iff.mpr hzp)
          have h2 : z ∈ Metric.ball ((chartAt ℂ x) x) σ ∩ {p} :=
            ⟨hzs, Set.mem_singleton_iff.mpr hzp⟩
          rw [Pi.add_apply, Set.indicator_of_mem hzs, Set.indicator_of_notMem h1,
            Set.indicator_of_mem h2, zero_add]
        · have h1 : z ∈ Metric.ball ((chartAt ℂ x) x) σ \ {p} := by
            rw [Set.mem_sdiff]
            exact ⟨hzs, fun h => hzp (Set.mem_singleton_iff.mp h)⟩
          have h2 : z ∉ Metric.ball ((chartAt ℂ x) x) σ ∩ {p} := by
            rw [Set.mem_inter_iff]
            exact fun h => hzp (Set.mem_singleton_iff.mp h.2)
          rw [Pi.add_apply, Set.indicator_of_mem hzs, Set.indicator_of_mem h1,
            Set.indicator_of_notMem h2, add_zero]
      · have h1 : z ∉ Metric.ball ((chartAt ℂ x) x) σ \ {p} := fun h => hzs h.1
        have h2 : z ∉ Metric.ball ((chartAt ℂ x) x) σ ∩ {p} := fun h => hzs h.1
        rw [Pi.add_apply, Set.indicator_of_notMem hzs, Set.indicator_of_notMem h1,
          Set.indicator_of_notMem h2, add_zero]
    rw [hdec]
    exact hmeas₁.add hmeas₂
  -- the dominating integrable function
  have hdom : Integrable (fun z : ℂ => C₁ * C₂ * ((‖z - p‖)⁻¹ * φ z)) := by
    have h := Work.Analysis.integrable_inv_norm_mul_of_hasCompactSupport p (fun z : ℂ => φ z)
      φ.continuous φ.hasCompactSupport
    simpa using h.const_mul (C₁ * C₂)
  -- the pointwise-a.e. bound
  have hae_ne : ∀ᵐ z ∂(volume : Measure ℂ), z ≠ p := by
    rw [MeasureTheory.ae_iff]
    simp
  have hbound : ∀ᵐ z ∂(volume : Measure ℂ),
      ‖(fun z : ℂ => Work.Drive.clampedPullback x σ W z *
        inner (𝕜 := ℝ) (gradient (Work.Drive.clampedPullback x ρ f) z)
          (gradient (Work.Drive.clampedPullback x ρ g) z)) z‖
        ≤ C₁ * C₂ * ((‖z - p‖)⁻¹ * φ z) := by
    filter_upwards [hae_ne] with z hzp
    by_cases hz : z ∈ Metric.ball ((chartAt ℂ x) x) σ
    · have hzρ : z ∈ Metric.ball ((chartAt ℂ x) x) ρ :=
        Metric.ball_subset_ball (le_of_lt hσρ) hz
      have hzφ : z ∈ Metric.closedBall ((chartAt ℂ x) x) (rIn : ℝ) :=
        Metric.mem_closedBall.mpr
          (le_trans (le_of_lt (Metric.mem_ball.mp hz)) hσ_le_rIn)
      have hφz : φ z = 1 := φ.one_of_mem_closedBall hzφ
      have hkey : Work.Drive.clampedPullback x σ W z *
          inner (𝕜 := ℝ) (gradient (Work.Drive.clampedPullback x ρ f) z)
            (gradient (Work.Drive.clampedPullback x ρ g) z)
          = W ((chartAt ℂ x).symm z) * inner (𝕜 := ℝ)
              (gradient (fun w : ℂ => f ((chartAt ℂ x).symm w)) z)
              (gradient (fun w : ℂ => g ((chartAt ℂ x).symm w)) z) := by
        rw [Work.Drive.clampedPullback_apply_of_mem hz,
          gradient_clampedPullback_eq_of_mem_ball (x := x) (ρ := ρ) hzρ,
          gradient_clampedPullback_eq_of_mem_ball (x := x) (ρ := ρ) hzρ]
      rw [hkey, norm_mul]
      calc ‖W ((chartAt ℂ x).symm z)‖ *
            ‖inner (𝕜 := ℝ) (gradient (fun w : ℂ => f ((chartAt ℂ x).symm w)) z)
              (gradient (fun w : ℂ => g ((chartAt ℂ x).symm w)) z)‖
          ≤ C₁ * (C₂ / ‖z - p‖) :=
            mul_le_mul (hWbd z hz) (hgrad z hz hzp) (norm_nonneg _) hC₁
        _ = C₁ * C₂ * ((‖z - p‖)⁻¹ * φ z) := by
            rw [hφz, mul_one, div_eq_mul_inv]
            ring
    · have hkey : Work.Drive.clampedPullback x σ W z *
          inner (𝕜 := ℝ) (gradient (Work.Drive.clampedPullback x ρ f) z)
            (gradient (Work.Drive.clampedPullback x ρ g) z) = 0 := by
        rw [Work.Drive.clampedPullback_apply_of_notMem hz, zero_mul]
      rw [hkey, norm_zero]
      exact mul_nonneg (mul_nonneg hC₁ hC₂)
        (mul_nonneg (inv_nonneg.mpr (norm_nonneg _)) φ.nonneg)
  show Integrable (fun z : ℂ => Work.Drive.clampedPullback x σ W z *
        inner (𝕜 := ℝ) (gradient (Work.Drive.clampedPullback x ρ f) z)
          (gradient (Work.Drive.clampedPullback x ρ g) z))
  refine Integrable.mono' hdom ?_ hbound
  rw [hfun]
  exact hJmeas.aestronglyMeasurable

end Work.Kernel
