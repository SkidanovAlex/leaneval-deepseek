import Mathlib
import Submission.Work.Kernel.GreenCover

/-!
# Convergence of the gradients of a clamped pullback from eventual local equality

The `gradient` of a function is the Riesz representative of its Fréchet derivative, so it is
invariant under *local* (almost-everywhere in the point) equality: if `f =ᶠ[𝓝 z] g` then
`∇ f z = ∇ g z` (`Filter.EventuallyEq.gradient_eq`), because `fderiv` is.  Consequently, if for
almost every `z` the clamped pullbacks `clampedPullback x ρ (u n)` are eventually (in `n`) equal to
`clampedPullback x ρ w` in a neighbourhood of `z`, then for almost every `z` the gradients at `z`
are eventually *equal* to the gradient of `clampedPullback x ρ w` at `z`, hence converge to it.

The point of the lemma is that the convergence of the gradients is obtained **without any
regularity hypothesis** on the functions `u n` or `w`: no differentiability, no harmonicity, no
smoothness of the chart pullbacks.  This is what the `C¹`/analytic estimates of the energy route
(`Work.Drive.contDiffAt_clampedPullback`, `Work.Analysis.gradient_neg_log_norm`) consume.
-/

namespace Work.Analysis

theorem tendsto_gradient_clampedPullback {X : Type*} [TopologicalSpace X] [T2Space X]
    [ChartedSpace ℂ X] {x : X} {ρ : ℝ} {u : ℕ → X → ℝ} {w : X → ℝ}
    (h : ∀ᵐ z ∂(MeasureTheory.volume : MeasureTheory.Measure ℂ),
      ∀ᶠ n in Filter.atTop,
        Work.Drive.clampedPullback x ρ (u n) =ᶠ[nhds z] Work.Drive.clampedPullback x ρ w) :
    ∀ᵐ z ∂(MeasureTheory.volume : MeasureTheory.Measure ℂ),
      Filter.Tendsto (fun n => gradient (Work.Drive.clampedPullback x ρ (u n)) z) Filter.atTop
        (nhds (gradient (Work.Drive.clampedPullback x ρ w) z)) := by
  filter_upwards [h] with z hz
  -- the sequence of gradients is eventually constant, equal to the gradient of the limit function
  refine Filter.Tendsto.congr' ?_ tendsto_const_nhds
  filter_upwards [hz] with n hn
  exact (hn.gradient_eq).symm

end Work.Analysis
