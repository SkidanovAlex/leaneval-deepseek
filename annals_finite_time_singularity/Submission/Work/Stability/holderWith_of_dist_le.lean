import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts.BinaryProducts
import Mathlib.LinearAlgebra.CrossProduct
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Topology.MetricSpace.Holder
import Submission.Work.Stability.CutFactorFderivZero
import Submission.Work.Stability.Cutoff
import Submission.Work.Stability.OmegaCutSupport
import Submission.Work.Stability.mul_rpow_le
import Submission.Work.StabilityFar.Holder.holderOnWith_of_norm_le
-- ===== merged: Submission.Work.SolutionDelivery.Datum =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open FiniteTimeSingularity Set Gradient Matrix Filter Topology MeasureTheory
open scoped Topology Matrix NNReal ENNReal

namespace Work.SolutionDelivery

/-- **The `α`-power decay of the vorticity is automatic for a bounded compactly supported field.**

If `ω` vanishes outside `B(0,R)` and is bounded by `M`, then `‖ω x‖ ≤ C/(‖x‖^α + 1)` for every
`x`, with `C = max 1 (M(R^α+1))`: outside the ball both sides vanish, and inside it
`‖x‖^α + 1 ≤ R^α + 1` so that `M ≤ C/(‖x‖^α+1)`. -/
theorem vorticityDecay_of_support_bdd {α : NNReal} {ω : R3 → R3} {R M : ℝ}
    (hR : 0 ≤ R) (hM : 0 ≤ M)
    (hsupp : ∀ y : R3, ω y ≠ 0 → y ∈ Metric.closedBall 0 R)
    (hbdd : ∀ y : R3, ‖ω y‖ ≤ M) :
    Work.LWP.VorticityDecay α ω := by
  refine ⟨max 1 (M * (R ^ (α : ℝ) + 1)), lt_of_lt_of_le one_pos (le_max_left _ _), fun x => ?_⟩
  rcases eq_or_ne (ω x) 0 with h0 | hne
  · rw [h0, norm_zero]
    positivity
  · have hxmem : x ∈ Metric.closedBall (0 : R3) R := hsupp x hne
    rw [Metric.mem_closedBall, dist_zero_right] at hxmem
    have hxα : ‖x‖ ^ (α : ℝ) ≤ R ^ (α : ℝ) :=
      Real.rpow_le_rpow (norm_nonneg x) hxmem (by positivity)
    have hden : 0 < ‖x‖ ^ (α : ℝ) + 1 := by
      have := Real.rpow_nonneg (norm_nonneg x) (α : ℝ); linarith
    have hdenR : 0 < R ^ (α : ℝ) + 1 := by
      have := Real.rpow_nonneg hR (α : ℝ); linarith
    rw [le_div_iff₀ hden]
    have h1 : M * (R ^ (α : ℝ) + 1) ≤ max 1 (M * (R ^ (α : ℝ) + 1)) := le_max_right _ _
    have h2 : 1 ≤ max 1 (M * (R ^ (α : ℝ) + 1)) := le_max_left _ _
    nlinarith [hbdd x, h1, h2, hdenR, hxα, Real.rpow_nonneg (norm_nonneg x) (α : ℝ)]

end Work.SolutionDelivery
end
end
-- ===== merged: Submission.Work.SolutionDelivery.Holder.timeHolderOnBall_of_isContDiffHolderOn =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.SolutionDelivery.Holder

open Set Metric
open scoped Topology

/-- Elementary real inequality: for `d ∈ [0, D]` and `0 ≤ α ≤ 1`, the identity map is bounded by
`max D 1 · d^α` on `[0, D]`.  (On a *bounded* interval every Lipschitz bound is an `α`-Hölder
bound, for every `α ≤ 1`.) -/
theorem self_le_max_mul_rpow {d D α : ℝ} (hd : 0 ≤ d) (hdD : d ≤ D) (hα0 : 0 ≤ α)
    (hα1 : α ≤ 1) : d ≤ max D 1 * d ^ α := by
  have hD1 : (1 : ℝ) ≤ max D 1 := le_max_right _ _
  have hD0 : (0 : ℝ) ≤ max D 1 := le_trans zero_le_one hD1
  rcases eq_or_lt_of_le hα0 with hα | hα
  · rw [← hα, Real.rpow_zero, mul_one]
    exact le_trans hdD (le_max_left _ _)
  · rcases eq_or_lt_of_le hd with hd0 | hdpos
    · rw [← hd0, Real.zero_rpow (ne_of_gt hα), mul_zero]
    · rcases le_or_gt d 1 with hd1 | hd1
      · have hle : d ≤ d ^ α := by
          have h := Real.rpow_le_rpow_of_exponent_ge hdpos hd1 hα1
          rwa [Real.rpow_one] at h
        calc d ≤ d ^ α := hle
          _ ≤ max D 1 * d ^ α :=
              le_mul_of_one_le_left (Real.rpow_nonneg (le_of_lt hdpos) α) hD1
      · have hle : (1 : ℝ) ≤ d ^ α := Real.one_le_rpow (le_of_lt hd1) hα0
        calc d ≤ D := hdD
          _ ≤ max D 1 := le_max_left _ _
          _ = max D 1 * 1 := (mul_one _).symm
          _ ≤ max D 1 * d ^ α := mul_le_mul_of_nonneg_left hle hD0


end Work.SolutionDelivery.Holder
end
-- ===== merged: Submission.Work.SolutionDelivery.Holder.timeHolderOnBall_timeDeriv_of_isContDiffHolderOn =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The time block of the core `C^{1,α}` regularity of `ω`

`Work.StabilityFar.TimeHolderOnBall α ω R T H` is the *time*-`α`-Hölder regularity of the
vorticity `ω` on the support ball `B(0,R)`, over the two-sided window `[-1,T+1]`:

  `‖ω z t - ω z τ‖ ≤ H |t-τ|^α`   for `z ∈ B(0,R)`, `t, τ ∈ window T`.

`St4` (the far-field estimate) consumes this for the *vorticity itself* **and** for its time
derivative `∂ₜω = timeDeriv ω`.  This file delivers the second one from the core `C^{1,α}`
regularity of `ω.uncurry`, on the slightly larger ball `B(0,ρ)` with `R < ρ`: the time block of
the joint derivative `D(ω.uncurry)` *is* `∂ₜω` (`Work.StabilityFar.Deriv.hasFDerivAt_uncurry_apply`),
and the `α`-Hölder bound on `D(ω.uncurry)` on the core strip is exactly the hypothesis `hcore`.

The strict inequality `R < ρ` is what makes the boundary of the support ball `B(0,R)` an
*interior* point of the core region `B(0,ρ)`; there `fderivWithin` agrees with `fderiv` and the
uncurried field is genuinely differentiable, so the block identity applies.
-/

namespace Work.SolutionDelivery.Holder

open Set Metric FiniteTimeSingularity
open scoped Topology NNReal



end Work.SolutionDelivery.Holder
end
-- ===== merged: Submission.Work.SolutionDelivery.Integrable.integrable_of_support_subset_closedBall =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.SolutionDelivery.Integrable

open MeasureTheory

/-- A function on `ℝ³` that is almost-everywhere strongly measurable, vanishes outside
`B(0,R)`, and is pointwise bounded by `M`, is integrable. -/
theorem integrable_of_support_subset_closedBall {f : Work.SolutionDelivery.R3 → Work.SolutionDelivery.R3} {R M : ℝ}
    (hmeas : MeasureTheory.AEStronglyMeasurable f MeasureTheory.volume)
    (hsupp : ∀ x : Work.SolutionDelivery.R3, f x ≠ 0 → x ∈ Metric.closedBall 0 R)
    (hbdd : ∀ x : Work.SolutionDelivery.R3, ‖f x‖ ≤ M) :
    MeasureTheory.Integrable f MeasureTheory.volume := by
  have hsub : Function.support f ⊆ Metric.closedBall (0 : Work.SolutionDelivery.R3) R :=
    fun x hx => hsupp x (Function.mem_support.mp hx)
  have hIntOn : IntegrableOn f (Metric.closedBall (0 : Work.SolutionDelivery.R3) R) volume :=
    IntegrableOn.of_bound (MeasureTheory.measure_closedBall_lt_top (x := (0 : Work.SolutionDelivery.R3)) (r := R))
      hmeas.restrict M (Filter.Eventually.of_forall hbdd)
  exact (integrableOn_iff_integrable_of_support_subset hsub).mp hIntOn

end Work.SolutionDelivery.Integrable
end
-- ===== merged: Submission.Work.SolutionDelivery.Measurable.aestronglyMeasurable_of_contOn_closedBall =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.SolutionDelivery.Measurable

open MeasureTheory


end Work.SolutionDelivery.Measurable
end
-- ===== merged: Submission.Work.SolutionDelivery.Measurable.continuousOn_vorticity_of_contDiffOn =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.SolutionDelivery.Measurable

open scoped Matrix

/-- The curl (vorticity) of a continuous linear map `ℝ³ →L[ℝ] ℝ³`, in exactly the form in
which the curl of a differentiable field appears in `FiniteTimeSingularity.vorticity`:
`∇×L = ∑ᵢ eᵢ ×₃ (L eᵢ)`. -/
noncomputable def curlOf (L : R3 →L[ℝ] R3) : R3 :=
  WithLp.toLp 2 (∑ i, FiniteTimeSingularity.e i ⨯₃ (L (FiniteTimeSingularity.e i)))

/-- `curlOf` is continuous (it is a finite sum of compositions of the continuous linear maps
`L ↦ L (e i)` and the bilinear cross product with the fixed vector `e i`). -/
theorem continuous_curlOf : Continuous curlOf := by
  unfold curlOf
  fun_prop

/-- The spatial derivative of the time slice `y ↦ u y t` at `x` is the restriction of the
joint derivative `fderiv ℝ u.uncurry (x,t)` to the first factor `ℝ³ → ℝ³ × ℝ`. -/
theorem fderiv_slice_eq {u : R3 → ℝ → R3} {x : R3} {t : ℝ}
    (h : DifferentiableAt ℝ u.uncurry (x, t)) :
    fderiv ℝ (fun y => u y t) x
      = (fderiv ℝ u.uncurry (x, t)) ∘SL (ContinuousLinearMap.inl ℝ R3 ℝ) := by
  rw [show (fun y : R3 => u y t) = u.uncurry ∘ (fun y => (y, t)) from rfl]
  rw [fderiv_comp x h (hasFDerivAt_prodMk_left x t).differentiableAt]
  rw [(hasFDerivAt_prodMk_left x t).fderiv]

/-- The vorticity of a slice through the derivative of the joint field. -/
theorem vorticity_eq_curlOf {u : R3 → ℝ → R3} {x : R3} {t : ℝ}
    (h : DifferentiableAt ℝ u.uncurry (x, t)) :
    FiniteTimeSingularity.vorticity (fun y => u y t) x
      = curlOf ((fderiv ℝ u.uncurry (x, t)) ∘SL (ContinuousLinearMap.inl ℝ R3 ℝ)) := by
  simp only [FiniteTimeSingularity.vorticity, curlOf, fderiv_slice_eq h]

theorem continuousOn_vorticity_of_contDiffOn {u : Work.SolutionDelivery.R3 → ℝ → Work.SolutionDelivery.R3}
    {T R : ℝ}
    (hsmooth : ContDiffOn ℝ 1 u.uncurry (Set.univ ×ˢ Work.SolutionDelivery.extWindow T)) :
    ContinuousOn (fun p : Work.SolutionDelivery.R3 × ℝ =>
        FiniteTimeSingularity.vorticity (fun y => u y p.2) p.1)
      (Metric.closedBall 0 R ×ˢ Set.Icc (-1) (T + 1)) := by
  let K : Set (R3 × ℝ) := Metric.closedBall 0 R ×ˢ Set.Icc (-1) (T + 1)
  -- `K` sits in the open set on which `u.uncurry` is `C¹`
  have hKsub : K ⊆ Set.univ ×ˢ extWindow T := by
    rintro ⟨x, t⟩ ⟨-, ht⟩
    exact ⟨trivial, ⟨by linarith [ht.1], by linarith [ht.2]⟩⟩
  have hopen : IsOpen (Set.univ ×ˢ extWindow T : Set (R3 × ℝ)) :=
    isOpen_univ.prod (isOpen_extWindow T)
  -- the joint derivative is continuous on `K`
  have hderiv : ContinuousOn (fderiv ℝ u.uncurry) K :=
    (hsmooth.continuousOn_fderiv_of_isOpen hopen le_rfl).mono hKsub
  have hcomp : ContinuousOn
      (fun p : R3 × ℝ => (fderiv ℝ u.uncurry p) ∘SL (ContinuousLinearMap.inl ℝ R3 ℝ)) K :=
    hderiv.clm_comp continuousOn_const
  refine (continuous_curlOf.comp_continuousOn hcomp).congr ?_
  intro p hp
  have hdiff : DifferentiableAt ℝ u.uncurry p :=
    (hsmooth.differentiableOn one_ne_zero).differentiableAt
      (hopen.mem_nhds (hKsub hp))
  exact vorticity_eq_curlOf hdiff

end Work.SolutionDelivery.Measurable
end
-- ===== merged: Submission.Work.SolutionDelivery.Measurable.slicesMeasurable_of_core =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.SolutionDelivery.Measurable

open MeasureTheory

/-- **Measurability of the vorticity slices from the core regularity.**

The core `C¹` regularity of `ω.uncurry` on `coreRegion ρ ×ˢ extWindow T`, together with the
support box (the slices vanish outside `B(0,R) ⊆ B(0,ρ)`), makes every slice `ω · t` at a window
time `t` Borel measurable: a function which is continuous on the closed ball `B(0,ρ)` and vanishes
off it is Borel measurable, hence (as `ℝ³` is second countable) almost everywhere strongly
measurable. -/
theorem slicesMeasurable_of_core {ω : Work.SolutionDelivery.R3 → ℝ → Work.SolutionDelivery.R3}
    {ρ R T : ℝ} (hρ : R ≤ ρ)
    (hcont : ContDiffOn ℝ 1 ω.uncurry
      (Work.StabilityFar.coreRegion ρ ×ˢ Work.SolutionDelivery.extWindow T))
    (hsupp : ∀ t ∈ Work.SolutionDelivery.extWindow T, ∀ y : Work.SolutionDelivery.R3,
      ω y t ≠ 0 → y ∈ Metric.closedBall 0 R) :
    Work.StabilityFar.SlicesMeasurable ω T := by
  intro t ht
  -- the window sits inside the extended window, where the core regularity is imposed
  have ht_ext : t ∈ Work.SolutionDelivery.extWindow T :=
    Work.SolutionDelivery.window_subset_extWindow T ht
  -- the `t`-slice is continuous on the core region
  have hcont_slice : ContinuousOn (fun y : Work.SolutionDelivery.R3 => ω y t)
      (Work.StabilityFar.coreRegion ρ) := by
    refine (hcont.continuousOn.comp (f := fun y : Work.SolutionDelivery.R3 => (y, t)) ?_ ?_)
    · exact (continuous_id.prodMk continuous_const).continuousOn
    · intro y hy; exact ⟨hy, ht_ext⟩
  -- hence a.e. strongly measurable for the restricted measure
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
      have hmemR : y ∈ Metric.closedBall (0 : Work.SolutionDelivery.R3) R := hsupp t ht_ext y hne
      rw [Metric.mem_closedBall, dist_eq_norm, sub_zero] at hmemR
      exact hy (by rw [Work.StabilityFar.mem_coreRegion]; linarith)
  rw [heq] at hind
  exact hind

end Work.SolutionDelivery.Measurable
end
-- ===== merged: Submission.Work.SolutionDelivery.Measurable.slicesMeasurable_timeDeriv_of_core =====
section

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




end Work.SolutionDelivery.Measurable
end
-- ===== merged: Submission.Work.SolutionDelivery.Sup.ciSup_norm_vorticity_eq_ciSup_closedBall =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.SolutionDelivery.Sup

open Set Metric
open scoped Topology

/-- The `L^∞` norm of the vorticity slice `ω(·,t) = ∇×(u(·,t))` is unchanged if the full-space
supremum `⨆ x, ‖ω(x,t)‖` is replaced by the supremum over a ball that contains the support of
the slice.

The hypotheses are exactly the two boxes under which the supremum is computed in the assembly:
`hbdd` bounds the slice by `M` (so the supremum is honest), and `hsupp` says the slice vanishes
off `B(0,R)`.  Together with `0 ≤ R` (so that `B(0,R)` is non-empty, containing `0`) they give
`⨆ x, ‖ω(x,t)‖ = ⨆ x ∈ B(0,R), ‖ω(x,t)‖`. -/
theorem ciSup_norm_vorticity_eq_ciSup_closedBall {u : Work.SolutionDelivery.R3 → ℝ → Work.SolutionDelivery.R3}
    {R t M : ℝ} (hR : 0 ≤ R)
    (hbdd : ∀ x : Work.SolutionDelivery.R3,
      ‖FiniteTimeSingularity.vorticity (fun y => u y t) x‖ ≤ M)
    (hsupp : ∀ x : Work.SolutionDelivery.R3,
      FiniteTimeSingularity.vorticity (fun y => u y t) x ≠ 0 → x ∈ Metric.closedBall 0 R) :
    Work.LWP.vortLInf u t
      = ⨆ x ∈ Metric.closedBall 0 R,
          ‖FiniteTimeSingularity.vorticity (fun y => u y t) x‖ := by
  unfold Work.LWP.vortLInf
  set ω : Work.SolutionDelivery.R3 → ℝ :=
    fun x => ‖FiniteTimeSingularity.vorticity (fun y => u y t) x‖ with hω
  change (⨆ x, ω x) = ⨆ x ∈ Metric.closedBall 0 R, ω x
  -- the slice is nonnegative and bounded above by `M`
  have hω0 : ∀ x, 0 ≤ ω x := fun x => norm_nonneg _
  have hbddω : BddAbove (Set.range ω) := ⟨M, by rintro _ ⟨x, rfl⟩; exact hbdd x⟩
  have hmem0 : (0 : Work.SolutionDelivery.R3) ∈ Metric.closedBall 0 R := by
    rw [Metric.mem_closedBall, dist_self]; exact hR
  -- the truncated function `x ↦ ⨆ (_ : x ∈ B(0,R)), ω x` is bounded above (by `max M 0`)
  have hbdd2 : BddAbove (Set.range (fun x => ⨆ (_ : x ∈ Metric.closedBall 0 R), ω x)) := by
    refine ⟨max M 0, ?_⟩
    rintro _ ⟨x, rfl⟩
    change (⨆ (_ : x ∈ Metric.closedBall 0 R), ω x) ≤ max M 0
    by_cases hx : x ∈ Metric.closedBall 0 R
    · rw [ciSup_pos hx]
      have : ω x ≤ M := by rw [hω]; exact hbdd x
      exact le_trans this (le_max_left _ _)
    · rw [ciSup_neg hx, Real.sSup_empty]; exact le_max_right _ _
  -- consequently the restricted supremum is nonnegative
  have hRHSnonneg : (0:ℝ) ≤ ⨆ x ∈ Metric.closedBall 0 R, ω x := by
    have hle1 : (⨆ (_ : (0:Work.SolutionDelivery.R3) ∈ Metric.closedBall 0 R), ω 0)
        ≤ ⨆ x ∈ Metric.closedBall 0 R, ω x := le_ciSup hbdd2 0
    have hle2 : ω 0 ≤ (⨆ (_ : (0:Work.SolutionDelivery.R3) ∈ Metric.closedBall 0 R), ω 0) :=
      le_of_eq (ciSup_pos (f := fun _ => ω 0) hmem0).symm
    exact le_trans (hω0 0) (le_trans hle2 hle1)
  refine le_antisymm ?_ ?_
  · -- `⨆ x, ω x ≤ ⨆ x ∈ B(0,R), ω x`: the slice vanishes off the ball
    apply ciSup_le
    intro x
    by_cases hx : x ∈ Metric.closedBall 0 R
    · calc ω x = (⨆ (_ : x ∈ Metric.closedBall 0 R), ω x) :=
            (ciSup_pos (f := fun _ => ω x) hx).symm
          _ = (fun y => ⨆ (_ : y ∈ Metric.closedBall 0 R), ω y) x := rfl
          _ ≤ ⨆ y ∈ Metric.closedBall 0 R, ω y := le_ciSup hbdd2 x
    · have hx0 : ω x = 0 := by
        have hv : FiniteTimeSingularity.vorticity (fun y => u y t) x = 0 := by
          by_contra h
          exact hx (hsupp x h)
        rw [hω]
        simp [hv]
      rw [hx0]; exact hRHSnonneg
  · -- `⨆ x ∈ B(0,R), ω x ≤ ⨆ x, ω x`: forget the constraint `x ∈ B(0,R)`
    apply ciSup_le
    intro x
    change (⨆ (_ : x ∈ Metric.closedBall 0 R), ω x) ≤ ⨆ x, ω x
    by_cases hx : x ∈ Metric.closedBall 0 R
    · rw [ciSup_pos hx]; exact le_ciSup hbddω x
    · rw [ciSup_neg hx, Real.sSup_empty]; exact le_trans (hω0 0) (le_ciSup hbddω 0)

end Work.SolutionDelivery.Sup
end
-- ===== merged: Submission.Work.SolutionDelivery.Sup.continuousOn_ciSup_closedBall =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.SolutionDelivery.Sup

open Set Metric
open scoped Topology

/-- **The supremum over a closed ball of a jointly continuous family is continuous in the
time parameter.**

If `p ↦ F p.1 p.2` is continuous on `closedBall 0 R ×ˢ Icc a b`, then
`t ↦ ⨆ x ∈ closedBall 0 R, F x t` is continuous on `Icc a b`.

The closed ball is compact (finite-dimensionality of `ℝ³`), so `F` is uniformly continuous on
`closedBall 0 R ×ˢ Icc a b`; around each `t₀` this yields both bounds
`(⨆ x ∈ K, F x t) ≤ (⨆ x ∈ K, F x t₀) + ε` and `(⨆ x ∈ K, F x t₀) ≤ (⨆ x ∈ K, F x t) + ε`.
The `⨆ x ∈ K, ·` notation is the *nested* binder `⨆ x, ⨆ (_ : x ∈ K), ·`: points `x ∉ K`
contribute the junk value `sSup ∅ = 0`, which is where `hR` (so that `K` is a proper subset of
`ℝ³`) enters. -/
theorem continuousOn_ciSup_closedBall {F : Work.SolutionDelivery.R3 → ℝ → ℝ} {R a b : ℝ} (hR : 0 ≤ R)
    (hcont : ContinuousOn (fun p : Work.SolutionDelivery.R3 × ℝ => F p.1 p.2)
      (Metric.closedBall 0 R ×ˢ Set.Icc a b)) :
    ContinuousOn (fun t => ⨆ x ∈ Metric.closedBall 0 R, F x t) (Set.Icc a b) := by
  classical
  let K : Set Work.SolutionDelivery.R3 := Metric.closedBall 0 R
  let I : Set ℝ := Set.Icc a b
  change ContinuousOn (fun t => ⨆ x ∈ K, F x t) I
  have hKc : IsCompact K := isCompact_closedBall 0 R
  have hIc : IsCompact I := isCompact_Icc
  have hcont' : ContinuousOn (fun p : Work.SolutionDelivery.R3 × ℝ => F p.1 p.2) (K ×ˢ I) := hcont
  -- `K` is non-empty since `0 ∈ closedBall 0 R`.
  have hKne : K.Nonempty := by
    refine ⟨0, ?_⟩
    change (0 : Work.SolutionDelivery.R3) ∈ Metric.closedBall 0 R
    rw [Metric.mem_closedBall, dist_self]
    exact hR
  -- the spatial slice `x ↦ F x t` is continuous on `K`.
  have hslice : ∀ t ∈ I, ContinuousOn (fun x : Work.SolutionDelivery.R3 => F x t) K := by
    intro t ht
    have hmap : Set.MapsTo (fun x : Work.SolutionDelivery.R3 => (x, t)) K (K ×ˢ I) :=
      fun x hx => ⟨hx, ht⟩
    have hc : ContinuousOn (fun x : Work.SolutionDelivery.R3 => (x, t)) K :=
      (Continuous.prodMk_left t).continuousOn
    have h := hcont'.comp hc hmap
    simpa only [Function.comp_def] using h
  -- the extended family `x ↦ ⨆ (_ : x ∈ K), F x t` is bounded above.
  have hBdd : ∀ t ∈ I,
      BddAbove (Set.range (fun x : Work.SolutionDelivery.R3 => ⨆ (_ : x ∈ K), F x t)) := by
    intro t ht
    exact bddAbove_range_ciSup_mem hKc (hslice t ht)
  -- a point of `ℝ³` outside `K`; it contributes the junk value `0` to the supremum.
  obtain ⟨x1, hx1⟩ : ∃ x : Work.SolutionDelivery.R3, x ∉ K := by
    obtain ⟨x, hx⟩ := exists_notMem_closedBall_R3 R
    exact ⟨x, hx⟩
  have hg_nonneg : ∀ s ∈ I, 0 ≤ (⨆ x, ⨆ (_ : x ∈ K), F x s) := by
    intro s hs
    have hle := le_ciSup (hBdd s hs) x1
    change (⨆ (_ : x1 ∈ K), F x1 s) ≤ (⨆ x, ⨆ (_ : x ∈ K), F x s) at hle
    rw [ciSup_eq_ite, Real.sSup_empty, dite_eq_right hx1] at hle
    exact hle
  rw [Metric.continuousOn_iff]
  intro t0 ht0 ε hε
  have hε2 : (0:ℝ) < ε / 2 := by linarith
  have hu := Metric.uniformContinuousOn_iff.mp
    ((hKc.prod hIc).uniformContinuousOn_of_continuous hcont')
  obtain ⟨δ, hδpos, hδ⟩ := hu (ε/2) hε2
  refine ⟨δ, hδpos, ?_⟩
  intro t ht hdist
  have hdxy : ∀ x : Work.SolutionDelivery.R3,
      dist ((x, t) : Work.SolutionDelivery.R3 × ℝ) (x, t0) < δ := by
    intro x
    rw [Prod.dist_eq, max_lt_iff]
    exact ⟨by rw [dist_self]; exact hδpos, hdist⟩
  -- uniform control of one slice against the other
  have hclose : ∀ x : Work.SolutionDelivery.R3, x ∈ K → |F x t - F x t0| < ε / 2 := by
    intro x hx
    have h := hδ (x, t) ⟨hx, ht⟩ (x, t0) ⟨hx, ht0⟩ (hdxy x)
    simpa only [Real.dist_eq] using h
  have hupper : (⨆ x, ⨆ (_ : x ∈ K), F x t) ≤ (⨆ x, ⨆ (_ : x ∈ K), F x t0) + ε/2 := by
    refine ciSup_le (fun x => ?_)
    change (⨆ (_ : x ∈ K), F x t) ≤ (⨆ x, ⨆ (_ : x ∈ K), F x t0) + ε/2
    rw [ciSup_eq_ite, Real.sSup_empty]
    by_cases hx : x ∈ K
    · rw [dite_eq_left hx]
      have hle : F x t0 ≤ (⨆ x, ⨆ (_ : x ∈ K), F x t0) := by
        have h := le_ciSup (hBdd t0 ht0) x
        change (⨆ (_ : x ∈ K), F x t0) ≤ _ at h
        rw [ciSup_eq_ite, Real.sSup_empty, dite_eq_left hx] at h
        exact h
      have hlt : F x t - F x t0 < ε/2 := (abs_lt.mp (hclose x hx)).2
      linarith
    · rw [dite_eq_right hx]
      linarith [hg_nonneg t0 ht0]
  have hlower : (⨆ x, ⨆ (_ : x ∈ K), F x t0) ≤ (⨆ x, ⨆ (_ : x ∈ K), F x t) + ε/2 := by
    refine ciSup_le (fun x => ?_)
    change (⨆ (_ : x ∈ K), F x t0) ≤ (⨆ x, ⨆ (_ : x ∈ K), F x t) + ε/2
    rw [ciSup_eq_ite, Real.sSup_empty]
    by_cases hx : x ∈ K
    · rw [dite_eq_left hx]
      have hle : F x t ≤ (⨆ x, ⨆ (_ : x ∈ K), F x t) := by
        have h := le_ciSup (hBdd t ht) x
        change (⨆ (_ : x ∈ K), F x t) ≤ _ at h
        rw [ciSup_eq_ite, Real.sSup_empty, dite_eq_left hx] at h
        exact h
      have hlt : -(ε/2) < F x t - F x t0 := (abs_lt.mp (hclose x hx)).1
      linarith
    · rw [dite_eq_right hx]
      linarith [hg_nonneg t ht]
  rw [Real.dist_eq]
  change |(⨆ x, ⨆ (_ : x ∈ K), F x t) - (⨆ x, ⨆ (_ : x ∈ K), F x t0)| < ε
  have h1 : (⨆ x, ⨆ (_ : x ∈ K), F x t) - (⨆ x, ⨆ (_ : x ∈ K), F x t0) ≤ ε/2 := by linarith
  have h2 : (⨆ x, ⨆ (_ : x ∈ K), F x t0) - (⨆ x, ⨆ (_ : x ∈ K), F x t) ≤ ε/2 := by linarith
  have h3 := abs_sub_le_iff.mpr ⟨h1, h2⟩
  linarith

end Work.SolutionDelivery.Sup
end
-- ===== merged: Submission.Work.SolutionDelivery.Vorticity.vorticity_eq_of_bsSlice =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.SolutionDelivery.Vorticity

/-- **The vorticity of the constructed solution is the given field.**  On the window the
Biot–Savart dictionary `hbs` identifies each velocity slice `u(·,t)` with `BS(ω(·,t))`; for an
integrable, bounded, divergence-free vorticity slice the Biot–Savart law `hLaw` then says that
the curl of that field is the slice itself. -/
theorem vorticity_eq_of_bsSlice {u ω : Work.SolutionDelivery.R3 → ℝ → Work.SolutionDelivery.R3} {T : ℝ}
    (hLaw : Work.LWP.BiotSavartLaw)
    (hbs : Work.StabilityFar.IsBiotSavartSlice u ω T)
    (hint : ∀ t ∈ Work.StabilityFar.window T, MeasureTheory.Integrable (fun y : Work.SolutionDelivery.R3 => ω y t))
    (hbdd : ∀ t ∈ Work.StabilityFar.window T, IsBoundedFun (fun y : Work.SolutionDelivery.R3 => ω y t))
    (hdiv : ∀ t ∈ Work.StabilityFar.window T, FiniteTimeSingularity.div (fun y : Work.SolutionDelivery.R3 => ω y t) = 0) :
    ∀ t ∈ Work.StabilityFar.window T, ∀ x : Work.SolutionDelivery.R3,
      FiniteTimeSingularity.vorticity (fun y => u y t) x = ω x t := by
  intro t ht x
  have hslice : (fun y => u y t) = Work.LWP.biotSavart (fun y => ω y t) :=
    funext (fun y => hbs t ht y)
  rw [hslice]
  exact Work.LWP.vorticity_biotSavart hLaw (hint t ht) (hbdd t ht)
    (fun y => congrFun (hdiv t ht) y) x

end Work.SolutionDelivery.Vorticity
end
-- ===== merged: Submission.Work.Stability.OmegaCutHolder =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology NNReal
open MeasureTheory Set Filter

namespace Work.Stability

set_option autoImplicit false

/-! ## The radial cut-off factor -/

/-- The radial cut-off factor of `ℝ³`: `x ↦ chi(ρ(x)/L)` with `ρ(x) = ‖x‖` and `chi` the `C^∞`
bump of `Work.Stability.Cutoff`.  `omegaCut L ω = cutFactor L • ω`. -/
noncomputable def cutFactor (L : ℝ) : Work.Cyl.R3 → ℝ :=
  fun x => chi (Work.Cyl.rho x / L)

theorem cutFactor_apply (L : ℝ) (x : Work.Cyl.R3) :
    cutFactor L x = chi (Work.Cyl.rho x / L) := rfl

/-- `omegaCut` is multiplication by the cut-off factor. -/
theorem omegaCut_eq_smul (L : ℝ) (ω : Work.Cyl.R3 → Work.Cyl.R3) :
    omegaCut L ω = cutFactor L • ω := rfl

/-! ## Elementary boundedness API -/

/-- A function with uniformly bounded norm is `IsBoundedFun`. -/
theorem isBoundedFun_of_forall_norm_le {X : Type*} [PseudoMetricSpace X] {E : Type*}
    [SeminormedAddCommGroup E] {f : X → E} {C : ℝ} (h : ∀ x, ‖f x‖ ≤ C) : IsBoundedFun f :=
  isBounded_iff_forall_norm_le.mpr ⟨C, fun y hy => by
    obtain ⟨x, -, rfl⟩ := hy
    exact h x⟩

/-- An `IsBoundedFun` function has a uniform norm bound. -/
theorem exists_norm_le_of_isBoundedFun {X : Type*} [PseudoMetricSpace X] {E : Type*}
    [SeminormedAddCommGroup E] {f : X → E} (h : IsBoundedFun f) :
    ∃ C : ℝ, ∀ x, ‖f x‖ ≤ C := by
  obtain ⟨C, hC⟩ := isBounded_iff_forall_norm_le.mp h
  exact ⟨C, fun x => hC (f x) ⟨x, Set.mem_univ x, rfl⟩⟩

/-- A continuous function vanishing outside the ball of radius `R` is bounded: its image is
contained in the image of the compact ball together with `{0}`. -/
theorem isBoundedFun_of_continuous_of_eq_zero_of_norm_gt {E : Type*} [NormedAddCommGroup E]
    [ProperSpace E] {F : Type*} [NormedAddCommGroup F] {f : E → F} {R : ℝ}
    (hf : Continuous f) (hz : ∀ x, R < ‖x‖ → f x = 0) : IsBoundedFun f := by
  have hbig : Bornology.IsBounded ((f '' Metric.closedBall (0 : E) R) ∪ ({0} : Set F)) :=
    Bornology.IsBounded.union ((isCompact_closedBall (0 : E) R).image hf).isBounded
      (isCompact_singleton (x := (0 : F))).isBounded
  refine hbig.subset ?_
  rintro y ⟨x, -, rfl⟩
  by_cases hx : R < ‖x‖
  · exact Or.inr (by simp [hz x hx])
  · refine Or.inl ⟨x, ?_, rfl⟩
    rw [Metric.mem_closedBall, dist_eq_norm, sub_zero]
    exact not_lt.mp hx

/-! ## Bounded Lipschitz times bounded Hölder is Hölder -/

/-- **The product estimate** (for `α ≤ 1`): the pointwise product of a bounded Lipschitz scalar
function `c` with a bounded `α`-Hölder function `A` is `α`-Hölder, with constant
`M_c C_A + M_A max K (2 M_c)`.  The point is that `|c x - c y| ≤ min (K d) (2 M_c)` while
`min (K d) (2 M_c) ≤ max K (2 M_c) · d^α` for `α ≤ 1` (`d ≤ d^α` for `d ≤ 1` and `1 ≤ d^α` for
`d ≥ 1`). -/
theorem holder_smul_of_bounded_lipschitz {X : Type*} [PseudoMetricSpace X] {E : Type*}
    [SeminormedAddCommGroup E] [NormedSpace ℝ E] {α : NNReal} (hα : α ≤ 1) {K : NNReal}
    {c : X → ℝ} {A : X → E} (hc : IsBoundedFun c) (hcl : LipschitzWith K c)
    (hb : IsBoundedFun A) (hA : Holder α A) : Holder α (c • A) := by
  obtain ⟨Mc₀, hMc₀⟩ := exists_norm_le_of_isBoundedFun hc
  obtain ⟨MA₀, hMA₀⟩ := exists_norm_le_of_isBoundedFun hb
  obtain ⟨CA, hCA⟩ := hA
  set Mc : ℝ := max Mc₀ 0 with hMcdef
  set MA : ℝ := max MA₀ 0 with hMAdef
  have hMc : ∀ x, ‖c x‖ ≤ Mc := fun x => le_trans (hMc₀ x) (le_max_left _ _)
  have hMA : ∀ x, ‖A x‖ ≤ MA := fun x => le_trans (hMA₀ x) (le_max_left _ _)
  have hMc0 : 0 ≤ Mc := le_max_right _ _
  have hMA0 : 0 ≤ MA := le_max_right _ _
  have hK0 : (0 : ℝ) ≤ (K : ℝ) := K.coe_nonneg
  have hmax0 : 0 ≤ max (K : ℝ) (2 * Mc) := le_trans (by linarith) (le_max_right _ _)
  have hC0 : 0 ≤ Mc * (CA : ℝ) + MA * max (K : ℝ) (2 * Mc) :=
    add_nonneg (mul_nonneg hMc0 CA.coe_nonneg) (mul_nonneg hMA0 hmax0)
  refine ⟨⟨Mc * (CA : ℝ) + MA * max (K : ℝ) (2 * Mc), hC0⟩, holderWith_of_dist_le fun x y => ?_⟩
  have hcx : |c x| ≤ Mc := by
    have h := hMc x
    rwa [Real.norm_eq_abs] at h
  have hcy : |c y| ≤ Mc := by
    have h := hMc y
    rwa [Real.norm_eq_abs] at h
  have hAy : ‖A y‖ ≤ MA := hMA y
  have hdA : dist (A x) (A y) ≤ (CA : ℝ) * dist x y ^ (α : ℝ) := hCA.dist_le x y
  have hdc1 : |c x - c y| ≤ (K : ℝ) * dist x y := by
    have h := hcl.dist_le_mul x y
    rwa [Real.dist_eq] at h
  have hdc2 : |c x - c y| ≤ 2 * Mc := by
    calc |c x - c y| = dist (c x) (c y) := by rw [Real.dist_eq]
      _ ≤ dist (c x) 0 + dist 0 (c y) := dist_triangle _ _ _
      _ = |c x| + |c y| := by rw [Real.dist_eq, Real.dist_eq, sub_zero, zero_sub, abs_neg]
      _ ≤ 2 * Mc := by linarith
  have hdc : |c x - c y| ≤ max (K : ℝ) (2 * Mc) * dist x y ^ (α : ℝ) := by
    rcases lt_or_ge (dist x y) 1 with hd | hd
    · have hs : dist x y ≤ dist x y ^ (α : ℝ) :=
        Real.self_le_rpow_of_le_one dist_nonneg (le_of_lt hd) (by exact_mod_cast hα)
      calc |c x - c y| ≤ (K : ℝ) * dist x y := hdc1
        _ ≤ (K : ℝ) * dist x y ^ (α : ℝ) := mul_le_mul_of_nonneg_left hs hK0
        _ ≤ max (K : ℝ) (2 * Mc) * dist x y ^ (α : ℝ) :=
            mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg dist_nonneg _)
    · have hs : (1 : ℝ) ≤ dist x y ^ (α : ℝ) := Real.one_le_rpow hd α.coe_nonneg
      calc |c x - c y| ≤ 2 * Mc := hdc2
        _ ≤ (2 * Mc) * dist x y ^ (α : ℝ) := le_mul_of_one_le_right (by linarith) hs
        _ ≤ max (K : ℝ) (2 * Mc) * dist x y ^ (α : ℝ) :=
            mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.rpow_nonneg dist_nonneg _)
  have hdec : c x • A x - c y • A y = c x • (A x - A y) + (c x - c y) • A y := by
    rw [smul_sub, sub_smul]; abel
  calc dist (c x • A x) (c y • A y) = ‖c x • (A x - A y) + (c x - c y) • A y‖ := by
        rw [dist_eq_norm, hdec]
    _ ≤ ‖c x • (A x - A y)‖ + ‖(c x - c y) • A y‖ := norm_add_le _ _
    _ = |c x| * dist (A x) (A y) + |c x - c y| * ‖A y‖ := by
        rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, dist_eq_norm]
    _ ≤ Mc * ((CA : ℝ) * dist x y ^ (α : ℝ)) + (max (K : ℝ) (2 * Mc) * dist x y ^ (α : ℝ)) * MA :=
        add_le_add (mul_le_mul hcx hdA dist_nonneg hMc0)
          (mul_le_mul hdc hAy (norm_nonneg _) (mul_nonneg hmax0 (Real.rpow_nonneg dist_nonneg _)))
    _ = (Mc * (CA : ℝ) + MA * max (K : ℝ) (2 * Mc)) * dist x y ^ (α : ℝ) := by ring

/-! ## Boundedness and Lipschitzness of the cut-off factor -/

/-- The derivative of the cut-off factor vanishes off the ball of radius `2L`. -/
theorem cutFactor_fderiv_eq_zero {L : ℝ} (hL : 0 < L) {x : Work.Cyl.R3}
    (hx : 2 * L < Work.Cyl.rho x) : fderiv ℝ (cutFactor L) x = 0 :=
  CutFactorFderivZero hL hx


/-- The cut-off factor is bounded by `1` (`0 ≤ chi ≤ 1`). -/
theorem cutFactor_bounded (L : ℝ) : IsBoundedFun (cutFactor L) := by
  refine isBoundedFun_of_forall_norm_le (C := 1) fun x => ?_
  rw [Real.norm_eq_abs, cutFactor_apply, abs_le]
  exact ⟨by linarith [chi_nonneg (Work.Cyl.rho x / L)], chi_le_one (Work.Cyl.rho x / L)⟩

/-- The derivative of the cut-off factor is bounded: it is continuous (the cut-off factor is
`C^1`) and vanishes off the ball of radius `2L`. -/
theorem cutFactor_fderiv_bounded {L : ℝ} (hL : 0 < L) :
    IsBoundedFun (fderiv ℝ (cutFactor L)) := by
  refine isBoundedFun_of_continuous_of_eq_zero_of_norm_gt (R := 2 * L)
    ((CutFactorContDiff hL 1).continuous_fderiv one_ne_zero) fun x hx => ?_
  exact cutFactor_fderiv_eq_zero hL (by rw [Work.Cyl.rho_eq_norm]; exact hx)

/-- The cut-off factor is Lipschitz: it is differentiable with bounded derivative
(`cutFactor_fderiv_bounded`). -/
theorem cutFactor_lipschitz {L : ℝ} (hL : 0 < L) :
    ∃ K : NNReal, LipschitzWith K (cutFactor L) :=
  LipschitzOfBoundedFderiv ((CutFactorContDiff hL 1).differentiable one_ne_zero)
    (cutFactor_fderiv_bounded hL)

/-! ## The main theorem -/


end Work.Stability
end
end
-- ===== merged: Submission.Work.Stability.holderWith_of_dist_le =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.Stability

end Work.Stability
end
