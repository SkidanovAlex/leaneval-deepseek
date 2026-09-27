import Mathlib
import Submission.Work.Drive.energyGreenRung
import Submission.Work.Drive.greenEnergyQ
import Submission.Work.Drive.greenCover

/-!
# The glue lemmas for the chart-wise energy route

* `Work.Drive.gradient_finset_sum` — the gradient of a finite sum;
* `Work.Drive.pairTerm_congr_fun_left/right` — locality of `pairTerm` in its two *function*
  arguments with respect to the topological support of its weight;
* `Work.Drive.pairTerm_finset_sum`, `Work.Drive.pairTerm_weight_finset_sum`,
  `Work.Drive.pairing_finset_sum` — linearity of `pairTerm`/`pairing` in the weight and in the
  second function, over finite sums.
-/

open MeasureTheory Set Filter
open scoped Manifold Topology Gradient

noncomputable section

namespace Work.Drive

variable {X : Type*} [TopologicalSpace X] [T2Space X] [ChartedSpace ℂ X]

/-! ## The gradient of a finite sum -/

/-- The gradient of a finite sum of functions differentiable at `z`. -/
theorem gradient_finset_sum {ι : Type*} (s : Finset ι) (g : ι → ℂ → ℝ) {z : ℂ}
    (h : ∀ i ∈ s, DifferentiableAt ℝ (g i) z) :
    gradient (fun w : ℂ => ∑ i ∈ s, g i w) z = ∑ i ∈ s, gradient (g i) z := by
  have hfun : (fun w : ℂ => ∑ i ∈ s, g i w) = ∑ i ∈ s, g i := by
    funext w; rw [Finset.sum_apply]
  simp only [gradient, hfun]
  rw [fderiv_sum h, map_sum]

/-- The gradient of a finite sum, almost everywhere. -/
theorem gradient_finset_sum_ae {ι : Type*} (s : Finset ι) (g : ι → ℂ → ℝ)
    (h : ∀ i ∈ s, ∀ᵐ z ∂(volume : Measure ℂ), DifferentiableAt ℝ (g i) z) :
    ∀ᵐ z ∂(volume : Measure ℂ),
      gradient (fun w : ℂ => ∑ i ∈ s, g i w) z = ∑ i ∈ s, gradient (g i) z := by
  filter_upwards [(Filter.eventually_all_finset s).mpr h] with z hz
  exact gradient_finset_sum s g hz

/-! ## Locality in the function arguments -/

/-- **Locality of `pairTerm` in its second function.**  If two functions agree on the topological
support of the weight, the pairing terms coincide. -/
theorem pairTerm_congr_fun_left {x : X} {ρ σ : ℝ} {W f f' g : X → ℝ} (hWc : Continuous W)
    (htgt : Metric.ball ((chartAt ℂ x) x) ρ ⊆ (chartAt ℂ x).target) (hσρ : σ < ρ)
    (h : ∀ y ∈ tsupport W, f y = f' y) :
    pairTerm x ρ σ W f g = pairTerm x ρ σ W f' g := by
  rw [pairTerm, pairTerm]
  refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
  dsimp only
  by_cases hz : clampedPullback x σ W z = 0
  · rw [hz, zero_mul, zero_mul]
  · have hzball : z ∈ Metric.ball ((chartAt ℂ x) x) σ := by
      by_contra hc
      exact hz (clampedPullback_eq_zero_of_notMem_ball hc)
    have hzρ : z ∈ Metric.ball ((chartAt ℂ x) x) ρ :=
      Metric.ball_subset_ball (le_of_lt hσρ) hzball
    have hzsupp : (chartAt ℂ x).symm z ∈ Function.support W := by
      by_contra hc
      rw [Function.mem_support, not_not] at hc
      rw [clampedPullback_apply_of_mem hzball, hc] at hz
      exact hz rfl
    have hev : clampedPullback x ρ f =ᶠ[𝓝 z] clampedPullback x ρ f' := by
      have hopen : Function.support W ∈ 𝓝 ((chartAt ℂ x).symm z) :=
        hWc.isOpen_support.mem_nhds hzsupp
      have hcont : ∀ᶠ w in 𝓝 z, (chartAt ℂ x).symm w ∈ Function.support W :=
        ((chartAt ℂ x).continuousAt_symm (htgt hzρ)).eventually hopen
      filter_upwards [hcont, Metric.isOpen_ball.mem_nhds hzρ] with w hw hwρ
      rw [clampedPullback_apply_of_mem hwρ, clampedPullback_apply_of_mem hwρ,
        h _ (subset_tsupport _ hw)]
    rw [Filter.EventuallyEq.gradient_eq hev]

/-- **Locality of `pairTerm` in its third function.** -/
theorem pairTerm_congr_fun_right {x : X} {ρ σ : ℝ} {W f g g' : X → ℝ} (hWc : Continuous W)
    (htgt : Metric.ball ((chartAt ℂ x) x) ρ ⊆ (chartAt ℂ x).target) (hσρ : σ < ρ)
    (h : ∀ y ∈ tsupport W, g y = g' y) :
    pairTerm x ρ σ W f g = pairTerm x ρ σ W f g' := by
  rw [pairTerm, pairTerm]
  refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
  dsimp only
  by_cases hz : clampedPullback x σ W z = 0
  · rw [hz, zero_mul, zero_mul]
  · have hzball : z ∈ Metric.ball ((chartAt ℂ x) x) σ := by
      by_contra hc
      exact hz (clampedPullback_eq_zero_of_notMem_ball hc)
    have hzρ : z ∈ Metric.ball ((chartAt ℂ x) x) ρ :=
      Metric.ball_subset_ball (le_of_lt hσρ) hzball
    have hzsupp : (chartAt ℂ x).symm z ∈ Function.support W := by
      by_contra hc
      rw [Function.mem_support, not_not] at hc
      rw [clampedPullback_apply_of_mem hzball, hc] at hz
      exact hz rfl
    have hev : clampedPullback x ρ g =ᶠ[𝓝 z] clampedPullback x ρ g' := by
      have hopen : Function.support W ∈ 𝓝 ((chartAt ℂ x).symm z) :=
        hWc.isOpen_support.mem_nhds hzsupp
      have hcont : ∀ᶠ w in 𝓝 z, (chartAt ℂ x).symm w ∈ Function.support W :=
        ((chartAt ℂ x).continuousAt_symm (htgt hzρ)).eventually hopen
      filter_upwards [hcont, Metric.isOpen_ball.mem_nhds hzρ] with w hw hwρ
      rw [clampedPullback_apply_of_mem hwρ, clampedPullback_apply_of_mem hwρ,
        h _ (subset_tsupport _ hw)]
    rw [Filter.EventuallyEq.gradient_eq hev]

/-! ## Linearity over finite sums -/

/-- **Linearity of `pairTerm` in its second function over finite sums.** -/
theorem pairTerm_finset_sum {ι : Type*} (s : Finset ι) {x : X} {ρ σ : ℝ} {ψ f : X → ℝ}
    {χ : ι → X → ℝ}
    (h₁ : ∀ i ∈ s, ∀ᵐ z ∂(volume : Measure ℂ),
      DifferentiableAt ℝ (clampedPullback x ρ (χ i)) z)
    (h₂ : ∀ i ∈ s, PairIntegrable x ρ σ ψ f (χ i)) :
    pairTerm x ρ σ ψ f (∑ i ∈ s, χ i) = ∑ i ∈ s, pairTerm x ρ σ ψ f (χ i) := by
  classical
  have hclamp : clampedPullback x ρ (∑ i ∈ s, χ i)
      = fun z => ∑ i ∈ s, clampedPullback x ρ (χ i) z := by
    rw [clampedPullback_finset_sum]
    funext z
    rw [Finset.sum_apply]
  rw [pairTerm, hclamp]
  have heq : (fun z : ℂ => clampedPullback x σ ψ z *
        inner (𝕜 := ℝ) (gradient (clampedPullback x ρ f) z)
          (gradient (fun w : ℂ => ∑ i ∈ s, clampedPullback x ρ (χ i) w) z))
      =ᵐ[volume] (fun z : ℂ => ∑ i ∈ s, clampedPullback x σ ψ z *
        inner (𝕜 := ℝ) (gradient (clampedPullback x ρ f) z)
          (gradient (clampedPullback x ρ (χ i)) z)) := by
    filter_upwards [gradient_finset_sum_ae s (fun i => clampedPullback x ρ (χ i)) h₁] with z hz
    rw [hz, inner_sum, Finset.mul_sum]
  rw [integral_congr_ae heq, integral_finsetSum s h₂]
  simp only [pairTerm]

/-- **Linearity of `pairTerm` in its weight over finite sums.** -/
theorem pairTerm_weight_finset_sum {ι : Type*} (s : Finset ι) {x : X} {ρ σ : ℝ}
    {W : ι → X → ℝ} {f g : X → ℝ}
    (h : ∀ i ∈ s, PairIntegrable x ρ σ (W i) f g) :
    pairTerm x ρ σ (∑ i ∈ s, W i) f g = ∑ i ∈ s, pairTerm x ρ σ (W i) f g := by
  classical
  have hclamp : clampedPullback x σ (∑ i ∈ s, W i)
      = fun z => ∑ i ∈ s, clampedPullback x σ (W i) z := by
    rw [clampedPullback_finset_sum]
    funext z
    rw [Finset.sum_apply]
  rw [pairTerm, hclamp]
  have heq : (fun z : ℂ => (∑ i ∈ s, clampedPullback x σ (W i) z) *
        inner (𝕜 := ℝ) (gradient (clampedPullback x ρ f) z) (gradient (clampedPullback x ρ g) z))
      =ᵐ[volume] (fun z : ℂ => ∑ i ∈ s, clampedPullback x σ (W i) z *
        inner (𝕜 := ℝ) (gradient (clampedPullback x ρ f) z) (gradient (clampedPullback x ρ g) z)) :=
    Filter.Eventually.of_forall fun z => Finset.sum_mul ..
  rw [integral_congr_ae heq, integral_finsetSum s h]
  simp only [pairTerm]

/-- **Linearity of `pairing` in its second function over finite sums.** -/
theorem pairing_finset_sum {ι κ : Type*} [Fintype ι] [Fintype κ] {y : ι → X} {ρ σ : ι → ℝ}
    {ψ : ι → X → ℝ} {f : X → ℝ} {χ : κ → X → ℝ}
    (h₁ : ∀ i j, ∀ᵐ z ∂(volume : Measure ℂ),
      DifferentiableAt ℝ (clampedPullback (y i) (ρ i) (χ j)) z)
    (h₂ : ∀ i j, PairIntegrable (y i) (ρ i) (σ i) (ψ i) f (χ j)) :
    pairing y ρ σ ψ f (∑ j, χ j) = ∑ j, pairing y ρ σ ψ f (χ j) := by
  classical
  simp only [pairing]
  rw [Finset.sum_congr rfl (fun i (_ : i ∈ (Finset.univ : Finset ι)) =>
    pairTerm_finset_sum Finset.univ (fun j _ => h₁ i j) (fun j _ => h₂ i j)), Finset.sum_comm]

end Work.Drive
