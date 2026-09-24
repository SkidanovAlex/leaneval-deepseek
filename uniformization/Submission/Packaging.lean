import ChallengeDeps
import Submission.Holomorphic
import Submission.Helpers

/-!
# Packaging a bijective holomorphic map as a complex diffeomorphism

The two remaining routes to the uniformization theorem (the Green function and the extremal
function) both end with a *proper holomorphic map with a single simple zero*; the "degree one"
argument (`Submission.Endgame`) upgrades such a map to a **bijection**.  To obtain the conclusion
of the theorem we then have to package a bijective holomorphic map as a `Diffeomorph`, i.e. as an
element of `X ≃ₘ⟮mℂ, mℂ⟯ ℂ` (or `≃ₘ⟮mℂ, mℂ⟯ 𝔻`).

This module provides that packaging, in two layers:

* `Submission.contMDiff_of_analyticAt_charts`: a map whose chart representations are complex
  analytic is `ℂ`-smooth (this is the only place where the manifold-level `ContMDiff` API is used);

* `Submission.nonempty_diffeomorph_of_analytic_equiv`: a bijection with analytic charts *and
  continuous inverse* is a diffeomorphism;

* `Submission.analyticAt_chartAt_inv_of_analytic` and
  `Submission.continuous_inv_of_analytic`: for a bijection `e : X ≃ ℂ` which is analytic in charts
  with everywhere non-vanishing chart derivative, the inverse has analytic charts and is
  continuous (via the one-dimensional inverse function theorem);

* `Submission.nonempty_diffeomorph_plane_of_bijective` and
  `Submission.uniformization_of_bijective_to_plane`: the first disjunct of the conclusion.
-/

open LeanEval.Geometry
open scoped Manifold ContDiff Topology

set_option linter.unusedSectionVars false

noncomputable section

open Filter Set
open Classical
open TopologicalSpace

namespace Submission

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]

/-! ## From analytic charts to `ContMDiff` -/

/-- **A map whose chart representations are complex analytic is `ℂ`-smooth.** -/
theorem contMDiff_of_analyticAt_charts {Y : Type*} [TopologicalSpace Y] [ChartedSpace ℂ Y]
    [IsManifold (modelWithCornersSelf ℂ ℂ) 1 Y] {e : X → Y} (hcont : Continuous e)
    (h : ∀ x, AnalyticAt ℂ ((chartAt ℂ (e x)) ∘ e ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) x)) :
    ContMDiff mℂ mℂ ∞ e := by
  intro x
  rw [contMDiffAt_iff]
  refine ⟨hcont.continuousAt, ?_⟩
  have hcx : ContDiffAt ℂ ∞ ((chartAt ℂ (e x)) ∘ e ∘ (chartAt ℂ x).symm)
      ((chartAt ℂ x) x) := (h x).contDiffAt
  have hcoe : ⇑(extChartAt mℂ (e x)) = ⇑(chartAt ℂ (e x)) := by
    simp [extChartAt_coe, modelWithCornersSelf_coe]
  have hcoesymm : ⇑(extChartAt mℂ x).symm = ⇑(chartAt ℂ x).symm := by
    simp [extChartAt_coe_symm, modelWithCornersSelf_coe_symm]
  have hpt : (extChartAt mℂ x) x = (chartAt ℂ x) x := by
    simp [extChartAt_coe, modelWithCornersSelf_coe]
  have hFeq : ⇑(extChartAt mℂ (e x)) ∘ e ∘ ⇑(extChartAt mℂ x).symm
      = (chartAt ℂ (e x)) ∘ e ∘ (chartAt ℂ x).symm := by
    funext w
    simp only [Function.comp_apply]
    rw [hcoe, hcoesymm]
  rw [hFeq, hpt, ModelWithCorners.Boundaryless.range_eq_univ]
  exact hcx.contDiffWithinAt

/-! ## The packaging of a bijective analytic map -/

/-- **A bijection with analytic charts and continuous inverse is a complex diffeomorphism.** -/
theorem nonempty_diffeomorph_of_analytic_equiv {Y : Type*} [TopologicalSpace Y]
    [ChartedSpace ℂ Y] [IsManifold (modelWithCornersSelf ℂ ℂ) 1 Y]
    (e : X ≃ Y) (hc : Continuous e) (hc' : Continuous e.symm)
    (h : ∀ x, AnalyticAt ℂ ((chartAt ℂ (e x)) ∘ e ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) x))
    (h' : ∀ y, AnalyticAt ℂ ((chartAt ℂ (e.symm y)) ∘ e.symm ∘ (chartAt ℂ y).symm)
      ((chartAt ℂ y) y)) :
    Nonempty (X ≃ₘ⟮mℂ, mℂ⟯ Y) :=
  ⟨Diffeomorph.mk e (contMDiff_of_analyticAt_charts hc h)
    (contMDiff_of_analyticAt_charts hc' h')⟩

/-! ## The inverse function theorem for a bijection with target `ℂ` -/

variable {e : X ≃ ℂ}

/-- **The inverse of a bijection with analytic charts is continuous**, provided the chart derivative
of `e` never vanishes. -/
theorem continuous_inv_of_analytic (h : ∀ x, AnalyticAt ℂ (e ∘ (chartAt ℂ x).symm)
      ((chartAt ℂ x) x))
    (hderiv : ∀ x, deriv (e ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) x) ≠ 0) :
    Continuous e.symm := by
  rw [continuous_iff_continuousAt]
  intro y
  set x : X := e.symm y with hx
  set c : OpenPartialHomeomorph X ℂ := chartAt ℂ x with hc
  set φ : ℂ → ℂ := e ∘ c.symm with hφdef
  set z : ℂ := c x with hz
  have hφ : AnalyticAt ℂ φ z := by rw [hφdef, hz, hc]; exact h x
  have hd : deriv φ z ≠ 0 := by rw [hφdef, hz, hc]; exact hderiv x
  let i : ℂ ≃L[ℂ] ℂ := .unitsEquivAut ℂ (.mk0 (deriv φ z) hd)
  have hfd : HasStrictFDerivAt φ i.toContinuousLinearMap z := hφ.hasStrictDerivAt
  let e₂ : OpenPartialHomeomorph ℂ ℂ := hfd.toOpenPartialHomeomorph φ
  have he₂ : (e₂ : ℂ → ℂ) = φ := rfl
  have hzs : z ∈ e₂.source := HasStrictFDerivAt.mem_toOpenPartialHomeomorph_source hfd
  have hzt : φ z ∈ e₂.target := by rw [← he₂]; exact e₂.map_source hzs
  have hzsy : e₂.symm (φ z) = z := by
    rw [← he₂]
    exact e₂.left_inv hzs
  have hφz : φ z = y := by
    rw [hφdef, hz, hc, Function.comp_apply, c.left_inv (mem_chart_source ℂ x)]
    exact e.apply_symm_apply y
  -- the local inverse on `e₂.target` satisfies `e (c.symm (e₂.symm u)) = u`
  have hconv : ∀ u : ℂ, e₂ (e₂.symm u) = e (c.symm (e₂.symm u)) := by
    intro u
    rw [he₂, hφdef]
    rfl
  have hright : ∀ᶠ u in 𝓝 (φ z), e (c.symm (e₂.symm u)) = u := by
    filter_upwards [e₂.open_target.mem_nhds hzt] with u hu
    rw [← hconv u]
    exact e₂.right_inv hu
  have hev : e.symm =ᶠ[𝓝 (φ z)] (c.symm ∘ (e₂.symm : ℂ → ℂ)) := by
    filter_upwards [hright] with u hu
    refine e.injective ?_
    rw [e.apply_symm_apply]
    exact hu.symm
  have hcont : ContinuousAt (c.symm ∘ (e₂.symm : ℂ → ℂ)) (φ z) := by
    refine ContinuousAt.comp (g := ⇑c.symm) (f := (e₂.symm : ℂ → ℂ)) ?_ ?_
    · rw [hzsy]
      exact c.continuousAt_symm (c.map_source (mem_chart_source ℂ x))
    · exact e₂.symm.continuousAt (by rw [OpenPartialHomeomorph.symm_source]; exact hzt)
  rw [← hφz]
  exact hcont.congr hev.symm

/-- **The inverse of a bijection with analytic charts has analytic charts**, provided the chart
derivative of `e` never vanishes. -/
theorem analyticAt_chartAt_inv_of_analytic (h : ∀ x, AnalyticAt ℂ (e ∘ (chartAt ℂ x).symm)
      ((chartAt ℂ x) x))
    (hderiv : ∀ x, deriv (e ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) x) ≠ 0) (y : ℂ) :
    AnalyticAt ℂ ((chartAt ℂ (e.symm y)) ∘ e.symm) y := by
  set x : X := e.symm y with hx
  set c : OpenPartialHomeomorph X ℂ := chartAt ℂ x with hc
  set φ : ℂ → ℂ := e ∘ c.symm with hφdef
  set z : ℂ := c x with hz
  have hφ : AnalyticAt ℂ φ z := by rw [hφdef, hz, hc]; exact h x
  have hd : deriv φ z ≠ 0 := by rw [hφdef, hz, hc]; exact hderiv x
  let i : ℂ ≃L[ℂ] ℂ := .unitsEquivAut ℂ (.mk0 (deriv φ z) hd)
  have hfd : HasStrictFDerivAt φ i.toContinuousLinearMap z := hφ.hasStrictDerivAt
  let e₂ : OpenPartialHomeomorph ℂ ℂ := hfd.toOpenPartialHomeomorph φ
  have he₂ : (e₂ : ℂ → ℂ) = φ := rfl
  have hzs : z ∈ e₂.source := HasStrictFDerivAt.mem_toOpenPartialHomeomorph_source hfd
  have hzt : φ z ∈ e₂.target := by rw [← he₂]; exact e₂.map_source hzs
  have hzsy : e₂.symm (φ z) = z := by
    rw [← he₂]
    exact e₂.left_inv hzs
  have hr_an : AnalyticAt ℂ (e₂.symm : ℂ → ℂ) (φ z) := by
    refine OpenPartialHomeomorph.analyticAt_symm (f := e₂) (a := φ z) (i := i) hzt ?_ ?_
    · rw [hzsy, he₂]
      exact hφ
    · rw [hzsy, he₂]
      exact hfd.hasFDerivAt.fderiv
  have hφz : φ z = y := by
    rw [hφdef, hz, hc, Function.comp_apply, c.left_inv (mem_chart_source ℂ x)]
    exact e.apply_symm_apply y
  have hcont_r : ContinuousAt (e₂.symm : ℂ → ℂ) (φ z) :=
    e₂.symm.continuousAt (by rw [OpenPartialHomeomorph.symm_source]; exact hzt)
  have htarget : ∀ᶠ u in 𝓝 (φ z), (e₂.symm : ℂ → ℂ) u ∈ c.target := by
    refine hcont_r.eventually ?_
    rw [hzsy, hz, hc]
    exact c.open_target.mem_nhds (c.map_source (mem_chart_source ℂ x))
  have hev2 : (c ∘ (c.symm ∘ (e₂.symm : ℂ → ℂ))) =ᶠ[𝓝 (φ z)] (e₂.symm : ℂ → ℂ) := by
    filter_upwards [htarget] with u hu
    simp only [Function.comp_apply]
    exact c.right_inv hu
  have hmain : AnalyticAt ℂ (c ∘ (c.symm ∘ (e₂.symm : ℂ → ℂ))) (φ z) :=
    hr_an.congr hev2.symm
  have hconv : ∀ u : ℂ, e₂ (e₂.symm u) = e (c.symm (e₂.symm u)) := by
    intro u
    rw [he₂, hφdef]
    rfl
  have hright : ∀ᶠ u in 𝓝 (φ z), e (c.symm (e₂.symm u)) = u := by
    filter_upwards [e₂.open_target.mem_nhds hzt] with u hu
    rw [← hconv u]
    exact e₂.right_inv hu
  have hev : e.symm =ᶠ[𝓝 (φ z)] (c.symm ∘ (e₂.symm : ℂ → ℂ)) := by
    filter_upwards [hright] with u hu
    refine e.injective ?_
    rw [e.apply_symm_apply]
    exact hu.symm
  have hevc : (c ∘ (c.symm ∘ (e₂.symm : ℂ → ℂ))) =ᶠ[𝓝 (φ z)] (c ∘ ⇑e.symm) := by
    filter_upwards [hev] with u hu
    simp only [Function.comp_apply] at hu ⊢
    rw [hu]
  rw [← hφz]
  exact (analyticAt_congr hevc).mp hmain

/-! ## Applications -/

/-- **A bijective holomorphic `X → ℂ` with non-vanishing chart derivative is a complex
diffeomorphism onto `ℂ`.** -/
theorem nonempty_diffeomorph_plane_of_bijective {Φ : X → ℂ} (hΦ : HolomorphicOnX Φ univ)
    (hbij : Function.Bijective Φ)
    (hderiv : ∀ x, deriv (Φ ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) x) ≠ 0) :
    Nonempty (X ≃ₘ⟮mℂ, mℂ⟯ ℂ) := by
  let e : X ≃ ℂ := Equiv.ofBijective Φ hbij
  have hcoe : ⇑e = Φ := Equiv.coe_ofBijective Φ hbij
  have hcont : Continuous e := by
    rw [hcoe]
    exact hΦ.continuous
  have han : ∀ x, AnalyticAt ℂ (e ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) x) := by
    intro x
    rw [hcoe]
    exact hΦ x (mem_univ x)
  have hd : ∀ x, deriv (e ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) x) ≠ 0 := by
    intro x
    rw [hcoe]
    exact hderiv x
  refine nonempty_diffeomorph_of_analytic_equiv e hcont (continuous_inv_of_analytic han hd) ?_ ?_
  · intro x
    rw [show (chartAt ℂ (e x)) = OpenPartialHomeomorph.refl ℂ from chartAt_self_eq]
    simpa using han x
  · intro y
    have := analyticAt_chartAt_inv_of_analytic (e := e) han hd y
    rw [show (chartAt ℂ y) = OpenPartialHomeomorph.refl ℂ from chartAt_self_eq]
    simpa using this

/-- The first disjunct of the uniformization conclusion, from a bijective holomorphic map onto
`ℂ` with non-vanishing chart derivative. -/
theorem uniformization_of_bijective_to_plane {X : Type*} [TopologicalSpace X] [T2Space X]
    [ConnectedSpace X] [SecondCountableTopology X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X] {Φ : X → ℂ} (hΦ : HolomorphicOnX Φ univ)
    (hbij : Function.Bijective Φ)
    (hderiv : ∀ x, deriv (Φ ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) x) ≠ 0) :
    Nonempty (X ≃ₘ⟮mℂ, mℂ⟯ ℂ) ∨ Nonempty (X ≃ₘ⟮mℂ, mℂ⟯ UpperHalfPlane) :=
  Helpers.uniformization_of_plane (nonempty_diffeomorph_plane_of_bijective hΦ hbij hderiv).some

end Submission
