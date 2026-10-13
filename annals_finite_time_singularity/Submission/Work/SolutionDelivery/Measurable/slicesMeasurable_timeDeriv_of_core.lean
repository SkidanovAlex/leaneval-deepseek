import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.SolutionDelivery.Defs
import Submission.Work.StabilityFar.Decay.aestronglyMeasurable_timeDeriv_slice

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# Measurability of the *time derivative* slices from the core regularity

`Work.StabilityFar.SlicesMeasurable (timeDeriv ω) T` is one of the two measurability inputs of
the far-field part of the Stability layer (together with `SlicesMeasurable ω T`): it says that
for every window time `t ∈ [-1, T+1]` the slice `∂ₜω(·,t)` is almost everywhere strongly
measurable.

The hypothesis here is the *core* `C¹` regularity of the uncurried vorticity
`ω.uncurry` on `coreRegion ρ ×ˢ extWindow T` (i.e. the first half of the core `C^{1,α}`
hypothesis `hωcore` of `ConstructedSolution`), together with the support box
`B(0,R) ⊆ B(0,ρ)`.

Why the *extended* window matters: `∂ₜω(·,t) = (deriv (ω y)) t` is a **two-sided** derivative, so
at a boundary point of the physical window (`t = -1` or `t = T+1`) it needs information about `ω`
on both sides of `t`, i.e. on `(-2, -1)` and on `(T+1, T+2)` respectively — outside the window
that `SlicesMeasurable` speaks about.  That information is available: the core regularity and the
support box are imposed on the extended window `(-2, T+2)`, and both are used below (the support
box to make the slices vanish identically *near* the far region, the differentiability on the
core strip to produce the slope quotients).

The strategy is the elementary one of
`Work.StabilityFar.Decay.aestronglyMeasurable_timeDeriv_slice`:

* for every `y` and every time `s` in a two-sided neighbourhood of `t` inside `extWindow T`, the
  time slice `s' ↦ ω y s'` is differentiable at `s` with derivative `∂ₜω y s` — on the core ball
  this is the chain rule applied to the (smooth) curve `s' ↦ (y, s')` composed with the core
  `C¹` regularity of `ω.uncurry`, and off the core ball the slice is *identically zero* on the
  whole extended window and the derivative vanishes;
* every slice `ω · s` for `s ∈ extWindow T` is a.e. strongly measurable (continuity on the core
  ball + vanishing off `B(0,R)` — the `extWindow` form of
  `Work.SolutionDelivery.Measurable.slicesMeasurable_of_core`);

so `∂ₜω(·,t)` is an everywhere-pointwise limit of strongly measurable difference quotients.
-/

namespace Work.SolutionDelivery.Measurable

open MeasureTheory Filter Topology Set

/-- **The slices of `ω` are a.e. strongly measurable on the whole extended window.**

This is the `extWindow` form of `slicesMeasurable_of_core` (whose stated conclusion only covers
the physical window `[-1, T+1]`): a slice `ω · t` is continuous on the closed core ball
`B(0,ρ)`, hence a.e. strongly measurable for the restricted measure there, and it vanishes off
`B(0,R) ⊆ B(0,ρ)`, so the indicator of the core ball is the slice itself. -/
theorem aestronglyMeasurable_slice_of_core_extWindow
    {ω : Work.SolutionDelivery.R3 → ℝ → Work.SolutionDelivery.R3} {ρ R T : ℝ} (hρ : R ≤ ρ)
    (hcont : ContDiffOn ℝ 1 ω.uncurry
      (Work.StabilityFar.coreRegion ρ ×ˢ Work.SolutionDelivery.extWindow T))
    (hsupp : ∀ t ∈ Work.SolutionDelivery.extWindow T, ∀ y : Work.SolutionDelivery.R3,
      ω y t ≠ 0 → y ∈ Metric.closedBall 0 R) :
    ∀ t ∈ Work.SolutionDelivery.extWindow T, AEStronglyMeasurable (ω · t) volume := by
  intro t ht
  -- the `t`-slice is continuous on the core region
  have hcont_slice : ContinuousOn (fun y : Work.SolutionDelivery.R3 => ω y t)
      (Work.StabilityFar.coreRegion ρ) := by
    refine (hcont.continuousOn.comp (f := fun y : Work.SolutionDelivery.R3 => (y, t)) ?_ ?_)
    · exact (continuous_id.prodMk continuous_const).continuousOn
    · intro y hy; exact ⟨hy, ht⟩
  have hmeas : AEStronglyMeasurable (fun y : Work.SolutionDelivery.R3 => ω y t)
      (volume.restrict (Work.StabilityFar.coreRegion ρ)) :=
    hcont_slice.aestronglyMeasurable (Work.StabilityFar.isClosed_coreRegion ρ).measurableSet
  have hind : AEStronglyMeasurable
      ((Work.StabilityFar.coreRegion ρ).indicator (fun y : Work.SolutionDelivery.R3 => ω y t))
      volume :=
    (aestronglyMeasurable_indicator_iff
      (Work.StabilityFar.isClosed_coreRegion ρ).measurableSet).mpr hmeas
  -- the slice already vanishes off the (closed) core ball, so the indicator is the slice itself
  have heq : (Work.StabilityFar.coreRegion ρ).indicator (fun y : Work.SolutionDelivery.R3 => ω y t)
      = (fun y => ω y t) := by
    funext y
    rcases em (y ∈ Work.StabilityFar.coreRegion ρ) with hy | hy
    · rw [Set.indicator_of_mem hy]
    · rw [Set.indicator_of_notMem hy]
      symm
      by_contra hne
      have hmemR : y ∈ Metric.closedBall (0 : Work.SolutionDelivery.R3) R := hsupp t ht y hne
      rw [Metric.mem_closedBall, dist_eq_norm, sub_zero] at hmemR
      exact hy (by rw [Work.StabilityFar.mem_coreRegion]; linarith)
  rw [heq] at hind
  exact hind

/-- **The time slices of `ω` are differentiable, with derivative `∂ₜω`, on the extended window.**

For every `t ∈ extWindow T` and every `y : ℝ³`, the slice `s' ↦ ω y s'` has derivative
`∂ₜω y t` at `t`:

* if `‖y‖ ≤ ρ` the curve `s' ↦ (y, s')` maps a neighbourhood of `t` into the core strip on which
  `ω.uncurry` is `C¹`, so the chain rule gives differentiability of the slice (and `deriv` is that
  derivative, by `hasDerivAt_deriv_iff`);
* otherwise `‖y‖ > ρ ≥ R`, and the support box forces `ω y s = 0` for *every* `s` in the extended
  window; the slice is then identically zero near `t` and its derivative is `0 = ∂ₜω y t`. -/
theorem hasDerivAt_timeDeriv_slice_of_core
    {ω : Work.SolutionDelivery.R3 → ℝ → Work.SolutionDelivery.R3} {ρ R T : ℝ} (hρ : R ≤ ρ)
    (hcont : ContDiffOn ℝ 1 ω.uncurry
      (Work.StabilityFar.coreRegion ρ ×ˢ Work.SolutionDelivery.extWindow T))
    (hsupp : ∀ t ∈ Work.SolutionDelivery.extWindow T, ∀ y : Work.SolutionDelivery.R3,
      ω y t ≠ 0 → y ∈ Metric.closedBall 0 R) :
    ∀ t ∈ Work.SolutionDelivery.extWindow T, ∀ y : Work.SolutionDelivery.R3,
      HasDerivAt (fun s' => ω y s') (FiniteTimeSingularity.timeDeriv ω y t) t := by
  intro t ht y
  by_cases hy : ‖y‖ ≤ ρ
  · -- `y` is in the core ball: compose the smooth curve `s' ↦ (y, s')` with the core `C¹` field
    have hdiff : DifferentiableAt ℝ (fun s' : ℝ => ω y s') t := by
      have hmaps : MapsTo (fun s' : ℝ => (y, s')) (Work.SolutionDelivery.extWindow T)
          (Work.StabilityFar.coreRegion ρ ×ˢ Work.SolutionDelivery.extWindow T) :=
        fun s' hs' => ⟨hy, hs'⟩
      have hcomp : ContDiffOn ℝ 1 (fun s' : ℝ => ω.uncurry (y, s'))
          (Work.SolutionDelivery.extWindow T) :=
        hcont.comp (by fun_prop) hmaps
      have hd : DifferentiableOn ℝ (fun s' : ℝ => ω y s')
          (Work.SolutionDelivery.extWindow T) := hcomp.differentiableOn (by norm_num)
      exact (hd t ht).differentiableAt ((Work.SolutionDelivery.isOpen_extWindow T).mem_nhds ht)
    have h := hasDerivAt_deriv_iff.mpr hdiff
    simpa only [FiniteTimeSingularity.timeDeriv] using h
  · -- `y` is strictly outside the core ball: the slice vanishes on the whole extended window
    have hygt : ρ < ‖y‖ := not_le.mp hy
    have hev : (fun s' : ℝ => ω y s') =ᶠ[𝓝 t]
        (fun _ => (0 : Work.SolutionDelivery.R3)) := by
      filter_upwards [(Work.SolutionDelivery.isOpen_extWindow T).mem_nhds ht] with s' hs'
      by_contra hne
      have hb := hsupp s' hs' y hne
      rw [Metric.mem_closedBall, dist_eq_norm, sub_zero] at hb
      exact absurd (le_trans hb hρ) (not_le.mpr hygt)
    have h0 : HasDerivAt (fun s' : ℝ => ω y s') (0 : Work.SolutionDelivery.R3) t :=
      hev.hasDerivAt_iff.mpr (hasDerivAt_const t 0)
    have hval : FiniteTimeSingularity.timeDeriv ω y t = 0 := by
      simp only [FiniteTimeSingularity.timeDeriv]
      rw [hev.deriv_eq, deriv_const]
    rw [hval]; exact h0

theorem slicesMeasurable_timeDeriv_of_core {ω : Work.SolutionDelivery.R3 → ℝ → Work.SolutionDelivery.R3}
    {ρ R T : ℝ} (hρ : R ≤ ρ)
    (hcore : IsContDiffHolderOn ℝ 0 ω.uncurry
      (Work.StabilityFar.coreRegion ρ ×ˢ Work.SolutionDelivery.extWindow T))
    (hsupp : ∀ t ∈ Work.SolutionDelivery.extWindow T, ∀ y : Work.SolutionDelivery.R3,
      ω y t ≠ 0 → y ∈ Metric.closedBall 0 R) :
    Work.StabilityFar.SlicesMeasurable (FiniteTimeSingularity.timeDeriv ω) T := by
  have hcont : ContDiffOn ℝ 1 ω.uncurry
      (Work.StabilityFar.coreRegion ρ ×ˢ Work.SolutionDelivery.extWindow T) := hcore.1
  have hdc := hasDerivAt_timeDeriv_slice_of_core hρ hcont hsupp
  have hmeas := aestronglyMeasurable_slice_of_core_extWindow hρ hcont hsupp
  intro t ht
  -- the physical window sits inside the extended one, where the core regularity lives
  rw [Work.StabilityFar.mem_window] at ht
  have ht_ext : t ∈ Work.SolutionDelivery.extWindow T :=
    ⟨by linarith [ht.1], by linarith [ht.2]⟩
  -- a two-sided window of times around `t`, contained in the extended window
  set ε : ℝ := min 1 (min (t + 2) (T + 2 - t)) with hεdef
  have hεpos : 0 < ε := by
    rw [hεdef]
    exact lt_min one_pos (lt_min (by linarith [ht.1]) (by linarith [ht.2]))
  have hε_le1 : ε ≤ t + 2 := (min_le_right _ _).trans (min_le_left _ _)
  have hε_le2 : ε ≤ T + 2 - t := (min_le_right _ _).trans (min_le_right _ _)
  have hsub : Set.Ioo (t - ε) (t + ε) ⊆ Work.SolutionDelivery.extWindow T := by
    intro s hs
    exact ⟨by linarith [hs.1, hε_le1], by linarith [hs.2, hε_le2]⟩
  exact Work.StabilityFar.Decay.aestronglyMeasurable_timeDeriv_slice hεpos
    (fun s hs y => hdc s (hsub hs) y) (fun s hs => hmeas s (hsub hs))

end Work.SolutionDelivery.Measurable
