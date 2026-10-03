import Mathlib
import Submission.Lib.Unif2.Work.CriticalSet.Defs
import Submission.Lib.Unif2.Work.CriticalSet.Fundamentals

/-!
# The critical points of a nowhere-locally-constant harmonic function are isolated

A replacement for Sard's lemma in the one-dimensional situation: a harmonic function on a Riemann
surface which is non-constant on every connected component of its domain has isolated critical
points.  Concretely, `Work.CriticalSet.IsDiscreteIn (criticalSet u U) U`.

The proof is local and analytic.  Near a point `x` the harmonic function `u` is the real part of a
holomorphic function `F` (`Submission.exists_holomorphicOnXAt_re_of_harmonic`); in the chart at `x`
its derivative is `deriv (F ∘ chart)`, whose zeros are isolated by analyticity (Mathlib's
`AnalyticAt.eventually_eq_zero_or_eventually_ne_zero`) unless the real part is locally constant.
The only remaining ingredient is the chart-change computation identifying "vanishing gradient of
`u` at `y`" with "vanishing derivative of the holomorphic companion in the chart at `x`", which is
`Work.CriticalSet.fderiv_chart_pullback_eq_zero_iff` below.

## Contents

* `Work.CriticalSet.tendsto_symm_chartAt` — the chart inverse is continuous at the image of its
  centre;
* `Work.CriticalSet.comp_eq_zero_iff_of_surjective`,
  `Work.CriticalSet.surjective_toSpanSingleton_restrictScalars` — elementary real-linear algebra;
* `Work.CriticalSet.fderiv_chart_pullback_eq_zero_iff` — the chart-change computation;
* `Work.CriticalSet.not_isCriticalPointAt_of_deriv_companion_ne_zero` — the pointwise conclusion;
* `Work.CriticalSet.criticalSet_isDiscreteIn` — the theorem.
-/

open LeanEval.Geometry
open scoped Manifold ContDiff Topology

set_option linter.unusedSectionVars false

noncomputable section

open Filter Set
open Classical

namespace Work.CriticalSet

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]

/-- The inverse of the preferred chart at `x` is continuous at `(chartAt ℂ x) x`. -/
theorem tendsto_symm_chartAt (x : X) :
    Tendsto (chartAt ℂ x).symm (𝓝 ((chartAt ℂ x) x)) (𝓝 x) := by
  have h : ContinuousAt (chartAt ℂ x).symm ((chartAt ℂ x) x) :=
    (chartAt ℂ x).continuousAt_symm (mem_chart_target ℂ x)
  rw [ContinuousAt] at h
  rwa [(chartAt ℂ x).left_inv (mem_chart_source ℂ x)] at h

/-- Composing with a surjective real-linear map `ℂ → ℂ`: the composite `A ∘L B` vanishes iff `A`
does. -/
theorem comp_eq_zero_iff_of_surjective {A : ℂ →L[ℝ] ℝ} {B : ℂ →L[ℝ] ℂ}
    (hB : Function.Surjective B) : A.comp B = 0 ↔ A = 0 := by
  refine ⟨fun h => ?_, fun h => by rw [h, ContinuousLinearMap.zero_comp]⟩
  ext v
  obtain ⟨w, rfl⟩ := hB v
  have := congrArg (fun (g : ℂ →L[ℝ] ℝ) => g w) h
  simpa using this

/-- Multiplication by a non-zero complex number, viewed as a real-linear endomorphism of `ℂ`, is
surjective. -/
theorem surjective_toSpanSingleton_restrictScalars {d : ℂ} (hd : d ≠ 0) :
    Function.Surjective ⇑((ContinuousLinearMap.toSpanSingleton ℂ d).restrictScalars ℝ) :=
  fun v => ⟨v / d, by simp [ContinuousLinearMap.toSpanSingleton_apply, div_mul_cancel₀ v hd]⟩

/-- **Change of chart for the vanishing of the derivative of a harmonic function.**

If `y` lies in the source of the preferred chart at `x`, then the real derivative of the pullback of
`u` to the chart at `x` vanishes at `(chartAt ℂ x) y` if and only if the real derivative of the
pullback of `u` to the preferred chart *at `y`* vanishes at `(chartAt ℂ y) y`; the latter is by
definition `IsCriticalPointAt u y`.

The two pullbacks are related by the chart transition `T = (chartAt ℂ x).symm ≫ₕ (chartAt ℂ y)`,
which is complex analytic at `(chartAt ℂ x) y` with non-zero derivative, hence a real-linear
surjection there; this reduces the claim to the elementary
`Work.CriticalSet.comp_eq_zero_iff_of_surjective`. -/
theorem fderiv_chart_pullback_eq_zero_iff {u : X → ℝ} {x y : X}
    (hyx : y ∈ (chartAt ℂ x).source) (hu : Submission.HarmonicOnXAt u y) :
    fderiv ℝ (u ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) y) = 0 ↔
      fderiv ℝ (u ∘ (chartAt ℂ y).symm) ((chartAt ℂ y) y) = 0 := by
  set T : ℂ → ℂ := ⇑((chartAt ℂ x).symm ≫ₕ (chartAt ℂ y)) with hT
  have hy : (chartAt ℂ x).symm ((chartAt ℂ x) y) = y := (chartAt ℂ x).left_inv hyx
  have hTy : T ((chartAt ℂ x) y) = (chartAt ℂ y) y := by
    rw [hT, OpenPartialHomeomorph.trans_apply, hy]
  have hmem : (chartAt ℂ x) y ∈ ((chartAt ℂ x).symm ≫ₕ (chartAt ℂ y)).source := by
    rw [OpenPartialHomeomorph.trans_source]
    refine ⟨(chartAt ℂ x).map_source hyx, ?_⟩
    simp only [Set.mem_preimage, hy]
    exact mem_chart_source ℂ y
  have hTana : AnalyticAt ℂ T ((chartAt ℂ x) y) := by
    have h := (Commons.Geometry.Manifold.chart_transition_analyticOnNhd x y) _ hmem
    simpa only [hT] using h
  have hTderiv : deriv T ((chartAt ℂ x) y) ≠ 0 := by
    rw [hT]
    exact chart_transition_deriv_ne_zero (x := y) (y := x) hyx
  have hTsurj : Function.Surjective ⇑(fderiv ℝ T ((chartAt ℂ x) y)) := by
    have hfd : fderiv ℝ T ((chartAt ℂ x) y)
        = (ContinuousLinearMap.toSpanSingleton ℂ (deriv T ((chartAt ℂ x) y))).restrictScalars ℝ :=
      (hTana.differentiableAt.hasDerivAt.hasFDerivAt.restrictScalars ℝ).fderiv
    rw [hfd]
    exact surjective_toSpanSingleton_restrictScalars hTderiv
  have hcont : Tendsto (chartAt ℂ x).symm (𝓝 ((chartAt ℂ x) y)) (𝓝 y) := by
    have h : ContinuousAt (chartAt ℂ x).symm ((chartAt ℂ x) y) :=
      (chartAt ℂ x).continuousAt_symm ((chartAt ℂ x).map_source hyx)
    rw [ContinuousAt] at h
    rwa [hy] at h
  have hEq : (u ∘ (chartAt ℂ x).symm) =ᶠ[𝓝 ((chartAt ℂ x) y)]
      ((u ∘ (chartAt ℂ y).symm) ∘ T) := by
    filter_upwards [hcont.eventually
      ((chartAt ℂ y).open_source.mem_nhds (mem_chart_source ℂ y))] with w hw
    simp only [Function.comp_apply, hT, OpenPartialHomeomorph.trans_apply]
    rw [(chartAt ℂ y).left_inv hw]
  have hTdiff : DifferentiableAt ℝ T ((chartAt ℂ x) y) :=
    hTana.differentiableAt.restrictScalars ℝ
  have hΨdiff : DifferentiableAt ℝ (u ∘ (chartAt ℂ y).symm) (T ((chartAt ℂ x) y)) := by
    rw [hTy]
    exact hu.1.differentiableAt (by norm_num)
  have hchain : fderiv ℝ (u ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) y)
      = fderiv ℝ (u ∘ (chartAt ℂ y).symm) ((chartAt ℂ y) y) ∘L fderiv ℝ T ((chartAt ℂ x) y) := by
    rw [hEq.fderiv_eq, fderiv_comp ((chartAt ℂ x) y) hΨdiff hTdiff, hTy]
  rw [hchain, comp_eq_zero_iff_of_surjective hTsurj]

/-- **The pointwise conclusion.**  If the holomorphic companion `F` of a harmonic `u` (in the chart
at `x`) has non-vanishing derivative at `c y := (chartAt ℂ x) y`, then `u` is not critical at the
point `y`. -/
theorem not_isCriticalPointAt_of_deriv_companion_ne_zero {u : X → ℝ} {F : X → ℂ} {x y : X}
    (hyx : y ∈ (chartAt ℂ x).source) (hu : Submission.HarmonicOnXAt u y)
    (hana : AnalyticAt ℂ (F ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) y))
    (hψ : (u ∘ (chartAt ℂ x).symm) =ᶠ[𝓝 ((chartAt ℂ x) y)]
      (fun w => (F ((chartAt ℂ x).symm w)).re))
    (hd : deriv (F ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) y) ≠ 0) :
    ¬ IsCriticalPointAt u y := by
  intro hcrit
  have hfd : fderiv ℝ (u ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) y) = 0 :=
    (fderiv_chart_pullback_eq_zero_iff hyx hu).mpr hcrit
  have h1 : fderiv ℝ (u ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) y)
      = fderiv ℝ (fun w => ((F ∘ (chartAt ℂ x).symm) w).re) ((chartAt ℂ x) y) :=
    hψ.fderiv_eq
  rw [h1] at hfd
  exact hd ((fderiv_re_eq_zero_iff hana).mp hfd)

/-- **The critical points of a nowhere-locally-constant harmonic function are isolated.**

If `u` is harmonic on the open set `U` and nowhere locally constant on `U` (i.e. `u` is nonconstant on
every connected component of `U`), then every point of `U` has a neighbourhood meeting the critical
set of `u` at most in that point.  This is the replacement for Sard's lemma: the critical points of a
nonconstant harmonic function are isolated.

Self-contained proof strategy (do NOT import sibling files under construction; helper results in the
same file are fine).

Fix `x ∈ U`.  Use `Submission.exists_holomorphicOnXAt_re_of_harmonic (hu x hx)` to get `F : X → ℂ`
holomorphic at `x` with `(fun y => (F y).re) =ᶠ u` near `x`.  Let `c := chartAt ℂ x`, `z := c x`,
`Φ := F ∘ c.symm`, `ψ := u ∘ c.symm`.  Then `Φ` is analytic at `z` (`HolomorphicOnXAt F x` *is*
`AnalyticAt ℂ Φ z` by definition), `ψ =ᶠ (fun w => (Φ w).re)` near `z`, and
`¬ ∀ᶠ w in nhds z, (Φ w).re = (Φ z).re` (pull the hypothesis `¬ ∀ᶠ y in nhds x, u y = u x` back along
the chart `c`, using `c.continuousAt` and `c.left_inv`, and note `ψ z = u x`).

* By `Work.CriticalSet.eventually_deriv_ne_zero_of_not_eventually_re_eq`,
  `∀ᶠ w in nhdsWithin z {z}ᶜ, deriv Φ w ≠ 0`; pulling back along `c` gives
  `∀ᶠ y in nhdsWithin x {x}ᶜ, deriv Φ (c y) ≠ 0`.
* Shrink to a chart ball around `x` inside `U ∩ c.source` on which `Φ` is analytic (use
  `isOpen_analyticAt`, `(chartAt ℂ x).open_source`, `(chartAt ℂ x).open_target`).  For `y ≠ x` in that
  set one has `¬ IsCriticalPointAt u y`: first show the chart-change step
  `IsCriticalPointAt u y ↔ fderiv ℝ ψ (c y) = 0` for `y ∈ U ∩ c.source` harmonic (put
  `T w := (chartAt ℂ y) (c.symm w)`, use `Work.CriticalSet.chart_transition_deriv_ne_zero` to see that
  the real derivative of `T` at `c y` — multiplication by the non-zero complex number `deriv T (c y)` —
  is onto, and the chain rule
  `fderiv ℝ ψ (c y) = (fderiv ℝ (u ∘ (chartAt ℂ y).symm) (c y)) ∘L (fderiv ℝ T (c y))`), then combine
  with `Work.CriticalSet.fderiv_re_eq_zero_iff` applied to `Φ` at `c y` (legitimate because `ψ` agrees
  with `fun w => (Φ w).re` near `c y` in the analytic ball, via `Filter.EventuallyEq.fderiv_eq`).

Conclude `∃ V ∈ nhds x, criticalSet u U ∩ V ⊆ {x}`. -/
theorem criticalSet_isDiscreteIn {X : Type*} [TopologicalSpace X] [T2Space X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X] {u : X → ℝ} {U : Set X}
    (hU : IsOpen U) (hu : Submission.HarmonicOnX u U) (hnlc : NotLocallyConstantOn u U) :
    IsDiscreteIn (criticalSet u U) U := by
  intro x hx
  obtain ⟨F, hF, hFre⟩ := Submission.exists_holomorphicOnXAt_re_of_harmonic (hu x hx)
  set c : OpenPartialHomeomorph X ℂ := chartAt ℂ x with hc
  set z : ℂ := c x with hz
  set Φ : ℂ → ℂ := F ∘ c.symm with hΦ
  have hxsrc : x ∈ c.source := mem_chart_source ℂ x
  have hΦana : AnalyticAt ℂ Φ z := hF
  -- `u ∘ c.symm` agrees with the real part of `Φ` near `z`
  have hψ : (u ∘ c.symm) =ᶠ[𝓝 z] (fun w => (Φ w).re) := by
    have hsymm : Tendsto c.symm (𝓝 z) (𝓝 x) := by
      have h : ContinuousAt c.symm z := c.continuousAt_symm (c.map_source hxsrc)
      rw [ContinuousAt] at h
      rwa [c.left_inv hxsrc] at h
    exact EventuallyEq.symm (hsymm.eventually hFre)
  -- `u` is not locally constant near `x`, so `Re Φ` is not locally constant near `z`
  have hnotconst : ¬ ∀ᶠ w in 𝓝 z, (Φ w).re = (Φ z).re := by
    intro hc'
    apply hnlc x hx
    have hzF : Φ z = F x := by
      simp only [hΦ, hz, hc, Function.comp_apply]
      rw [c.left_inv hxsrc]
    have hct : Tendsto c (𝓝 x) (𝓝 z) := c.continuousAt hxsrc
    filter_upwards [hct.eventually hc', c.open_source.eventually_mem hxsrc, hFre]
      with y hy hycsrc hFy
    have hy' : (F y).re = (F x).re := by
      have h1 : (Φ (c y)).re = (F y).re := by
        simp only [hΦ, Function.comp_apply]
        rw [c.left_inv hycsrc]
      have h2 : (Φ z).re = (F x).re := by rw [hzF]
      rw [← h1, ← h2]
      exact hy
    rw [← hFy, hy', hFre.eq_of_nhds]
  -- the derivative of `Φ` does not vanish away from `z`
  have hderiv : ∀ᶠ w in 𝓝[≠] z, deriv Φ w ≠ 0 :=
    eventually_deriv_ne_zero_of_not_eventually_re_eq hΦana hnotconst
  have hderiv' : ∀ᶠ w in 𝓝 z, w ≠ z → deriv Φ w ≠ 0 :=
    eventually_nhdsWithin_iff.mp hderiv
  have hψe : ∀ᶠ w in 𝓝 z, (u ∘ c.symm) w = (Φ w).re := hψ
  have hAll : ∀ᶠ w in 𝓝 z, AnalyticAt ℂ Φ w ∧ (w ≠ z → deriv Φ w ≠ 0) ∧
      ((u ∘ c.symm) w = (Φ w).re) :=
    ((isOpen_analyticAt ℂ Φ).eventually_mem hΦana).and (hderiv'.and hψe)
  obtain ⟨ρ, hρ, hball⟩ := Metric.mem_nhds_iff.mp hAll
  refine ⟨U ∩ c.source ∩ c ⁻¹' Metric.ball z ρ, ?_, ?_⟩
  · refine Filter.inter_mem (Filter.inter_mem (hU.mem_nhds hx) ?_) ?_
    · exact c.open_source.mem_nhds hxsrc
    · exact (c.continuousAt hxsrc).preimage_mem_nhds (Metric.ball_mem_nhds z hρ)
  · intro y hy
    obtain ⟨hycrit, hyV⟩ := hy
    obtain ⟨⟨hyU, hysrc⟩, hyball⟩ := hyV
    rw [Set.mem_singleton_iff]
    by_contra hyx
    have hcy_ne : c y ≠ z := fun h => hyx (c.injOn hysrc hxsrc h)
    have hcyball := hball hyball
    have hana0 : AnalyticAt ℂ Φ (c y) := hcyball.1
    have hd0 : deriv Φ (c y) ≠ 0 := hcyball.2.1 hcy_ne
    have hψ0 : (u ∘ c.symm) =ᶠ[𝓝 (c y)] (fun w => (Φ w).re) :=
      Filter.eventually_of_mem (Metric.isOpen_ball.mem_nhds hyball)
        (fun w hw => (hball hw).2.2)
    exact absurd hycrit.2
      (not_isCriticalPointAt_of_deriv_companion_ne_zero hysrc (hu y hyU) hana0 hψ0 hd0)

end Work.CriticalSet
